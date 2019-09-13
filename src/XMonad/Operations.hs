{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, PatternGuards, TypeSynonymInstances #-}
-- --------------------------------------------------------------------------
-- |
-- Module      :  XMonad.Operations
-- Copyright   :  (c) Spencer Janssen 2007
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  dons@cse.unsw.edu.au
-- Stability   :  unstable
-- Portability :  not portable, Typeable deriving, mtl, posix
--
-- Operations.
--
-----------------------------------------------------------------------------

module XMonad.Operations where

import XMonad.Core
import XMonad.Layout (Full(..))
import qualified XMonad.StackSet as W

import Data.Maybe
import Data.Monoid          (Endo(..),Any(..))
import Data.List            (nub, (\\), find)
import Data.Bits            ((.|.), (.&.), complement, testBit)
import Data.Ratio
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Applicative((<$>), (<*>))
import Control.Arrow (second)
import Control.Monad (void)
import Control.Monad.Reader
import Control.Monad.State
import qualified Control.Exception.Extensible as C

import System.IO
import System.Directory
import System.Posix.Process (executeFile)
import qualified Graphics.X11.Xlib as Xlib
import qualified Graphics.X11.Xinerama as Xlib (getScreenInfo)
import qualified Graphics.X11.Xlib.Extras as Xlib

-- ---------------------------------------------------------------------
-- |
-- Window manager operations
-- manage. Add a new window to be managed in the current workspace.
-- Bring it into focus.
--
-- Whether the window is already managed, or not, it is mapped, has its
-- border set, and its event mask set.
--
manage :: Xlib.Window -> X ()
manage w = whenX (not <$> isClient w) $ withDisplay $ \d -> do
    sh <- io $ Xlib.getWMNormalHints d w

    let isFixedSize = Xlib.sh_min_size sh /= Nothing && Xlib.sh_min_size sh == Xlib.sh_max_size sh
    isTransient <- isJust <$> io (Xlib.getTransientForHint d w)

    rr <- snd `fmap` floatLocation w
    -- ensure that float windows don't go over the edge of the screen
    let adjust (W.RationalRect x y wid h) | x + wid > 1 || y + h > 1 || x < 0 || y < 0
                                              = W.RationalRect (0.5 - wid/2) (0.5 - h/2) wid h
        adjust r = r

        f ws | isFixedSize || isTransient = W.float w (adjust rr) . W.insertUp w . W.view i $ ws
             | otherwise                  = W.insertUp w ws
            where i = W.tag $ W.workspace $ W.current ws

    mh <- asks (manageHook . config)
    g <- appEndo <$> userCodeDef (Endo id) (runQuery mh w)
    windows (g . f)

-- | unmanage. A window no longer exists, remove it from the window
-- list, on whatever workspace it is.
--
unmanage :: Xlib.Window -> X ()
unmanage = windows . W.delete

-- | Kill the specified window. If we do kill it, we'll get a
-- delete notify back from X.
--
-- There are two ways to delete a window. Either just kill it, or if it
-- supports the delete protocol, send a delete event (e.g. firefox)
--
killWindow :: Xlib.Window -> X ()
killWindow w = withDisplay $ \d -> do
    wmdelt <- atom_WM_DELETE_WINDOW  ;  wmprot <- atom_WM_PROTOCOLS

    protocols <- io $ Xlib.getWMProtocols d w
    io $ if wmdelt `elem` protocols
        then Xlib.allocaXEvent $ \ev -> do
                Xlib.setEventType ev Xlib.clientMessage
                Xlib.setClientMessageEvent ev w wmprot 32 wmdelt 0
                Xlib.sendEvent d w False Xlib.noEventMask ev
        else Xlib.killClient d w >> return ()

-- | Kill the currently focused client.
kill :: X ()
kill = withFocused killWindow

-- ---------------------------------------------------------------------
-- Managing windows

-- | windows. Modify the current window list with a pure function, and refresh
windows :: (WindowSet -> WindowSet) -> X ()
windows f = do
    XState { windowset = old } <- get
    let oldvisible = concatMap (W.integrate' . W.stack . W.workspace) $ W.current old : W.visible old
        newwindows = W.allWindows ws \\ W.allWindows old
        ws = f old
    XConf { display = d , normalBorder = nbc, focusedBorder = fbc } <- ask

    mapM_ setInitialProperties newwindows

    whenJust (W.peek old) $ \otherw -> do
      nbs <- asks (normalBorderColor . config)
      setWindowBorderWithFallback d otherw nbs nbc

    modify (\s -> s { windowset = ws })

    -- notify non visibility
    let tags_oldvisible = map (W.tag . W.workspace) $ W.current old : W.visible old
        gottenhidden    = filter (flip elem tags_oldvisible . W.tag) $ W.hidden ws
    mapM_ (sendMessageWithNoRefresh Hide) gottenhidden

    -- for each workspace, layout the currently visible workspaces
    let allscreens     = W.screens ws
        summed_visible = scanl (++) [] $ map (W.integrate' . W.stack . W.workspace) allscreens
    rects <- fmap concat $ forM (zip allscreens summed_visible) $ \ (w, vis) -> do
        let wsp   = W.workspace w
            this  = W.view n ws
            n     = W.tag wsp
            tiled = (W.stack . W.workspace . W.current $ this)
                    >>= W.filter (`M.notMember` W.floating ws)
                    >>= W.filter (`notElem` vis)
            viewrect = screenRect $ W.screenDetail w

        -- just the tiled windows:
        -- now tile the windows on this workspace, modified by the gap
        (rs, ml') <- runLayout wsp { W.stack = tiled } viewrect `catchX`
                     runLayout wsp { W.stack = tiled, W.layout = Layout Full } viewrect
        updateLayout n ml'

        let m   = W.floating ws
            flt = [(fw, scaleRationalRect viewrect r)
                    | fw <- filter (flip M.member m) (W.index this)
                    , Just r <- [M.lookup fw m]]
            vs = flt ++ rs

        io $ Xlib.restackWindows d (map fst vs)
        -- return the visible windows for this workspace:
        return vs

    let visible = map fst rects

    mapM_ (uncurry tileWindow) rects

    whenJust (W.peek ws) $ \w -> do
      fbs <- asks (focusedBorderColor . config)
      setWindowBorderWithFallback d w fbs fbc

    mapM_ reveal visible
    setTopFocus

    -- hide every window that was potentially visible before, but is not
    -- given a position by a layout now.
    mapM_ hide (nub (oldvisible ++ newwindows) \\ visible)

    -- all windows that are no longer in the windowset are marked as
    -- withdrawn, it is important to do this after the above, otherwise 'hide'
    -- will overwrite withdrawnState with iconicState
    mapM_ (flip setWMState Xlib.withdrawnState) (W.allWindows old \\ W.allWindows ws)

    isMouseFocused <- asks mouseFocused
    unless isMouseFocused $ clearEvents Xlib.enterWindowMask
    asks (logHook . config) >>= userCodeDef ()

-- | Modify the @WindowSet@ in state with no special handling.
modifyWindowSet :: (WindowSet -> WindowSet) -> X ()
modifyWindowSet f = modify $ \xst -> xst { windowset = f (windowset xst) }

-- | Perform an @X@ action and check its return value against a predicate p.
-- If p holds, unwind changes to the @WindowSet@ and replay them using @windows@.
windowBracket :: (a -> Bool) -> X a -> X a
windowBracket p action = withWindowSet $ \old -> do
  a <- action
  when (p a) . withWindowSet $ \new -> do
    modifyWindowSet $ \_ -> old
    windows         $ \_ -> new
  return a

-- | A version of @windowBracket@ that discards the return value, and handles an
-- @X@ action reporting its need for refresh via @Any@.
windowBracket_ :: X Any -> X ()
windowBracket_ = void . windowBracket getAny

-- | Produce the actual rectangle from a screen and a ratio on that screen.
scaleRationalRect :: Xlib.Rectangle -> W.RationalRect -> Xlib.Rectangle
scaleRationalRect (Xlib.Rectangle sx sy sw sh) (W.RationalRect rx ry rw rh)
 = Xlib.Rectangle (sx + scale sw rx) (sy + scale sh ry) (scale sw rw) (scale sh rh)
 where scale s r = floor (toRational s * r)

-- | setWMState.  set the WM_STATE property
setWMState :: Xlib.Window -> Int -> X ()
setWMState w v = withDisplay $ \dpy -> do
    a <- atom_WM_STATE
    io $ Xlib.changeProperty32 dpy w a a Xlib.propModeReplace [fromIntegral v, fromIntegral Xlib.none]

-- | Set the border color using the window's color map, if possible,
-- otherwise fallback to the color in @Pixel@.
setWindowBorderWithFallback :: Xlib.Display -> Xlib.Window -> String -> Xlib.Pixel -> X ()
setWindowBorderWithFallback dpy w color basic = io $
    C.handle fallback $ do
      wa <- Xlib.getWindowAttributes dpy w
      pixel <- Xlib.color_pixel . fst <$> Xlib.allocNamedColor dpy (Xlib.wa_colormap wa) color
      Xlib.setWindowBorder dpy w pixel
  where
    fallback :: C.SomeException -> IO ()
    fallback e = do hPrint stderr e >> hFlush stderr
                    Xlib.setWindowBorder dpy w basic

-- | hide. Hide a window by unmapping it, and setting Iconified.
hide :: Xlib.Window -> X ()
hide w = whenX (gets (S.member w . mapped)) $ withDisplay $ \d -> do
    cMask <- asks $ clientMask . config
    io $ do Xlib.selectInput d w (cMask .&. complement Xlib.structureNotifyMask)
            Xlib.unmapWindow d w
            Xlib.selectInput d w cMask
    setWMState w Xlib.iconicState
    -- this part is key: we increment the waitingUnmap counter to distinguish
    -- between client and xmonad initiated unmaps.
    modify (\s -> s { waitingUnmap = M.insertWith (+) w 1 (waitingUnmap s)
                    , mapped       = S.delete w (mapped s) })

-- | reveal. Show a window by mapping it and setting Normal
-- this is harmless if the window was already visible
reveal :: Xlib.Window -> X ()
reveal w = withDisplay $ \d -> do
    setWMState w Xlib.normalState
    io $ Xlib.mapWindow d w
    whenX (isClient w) $ modify (\s -> s { mapped = S.insert w (mapped s) })

-- | Set some properties when we initially gain control of a window
setInitialProperties :: Xlib.Window -> X ()
setInitialProperties w = asks normalBorder >>= \nb -> withDisplay $ \d -> do
    setWMState w Xlib.iconicState
    asks (clientMask . config) >>= io . Xlib.selectInput d w
    bw <- asks (borderWidth . config)
    io $ Xlib.setWindowBorderWidth d w bw
    -- we must initially set the color of new windows, to maintain invariants
    -- required by the border setting in 'windows'
    io $ Xlib.setWindowBorder d w nb

-- | refresh. Render the currently visible workspaces, as determined by
-- the 'StackSet'. Also, set focus to the focused window.
--
-- This is our 'view' operation (MVC), in that it pretty prints our model
-- with X calls.
--
refresh :: X ()
refresh = windows id

-- | clearEvents.  Remove all events of a given type from the event queue.
clearEvents :: Xlib.EventMask -> X ()
clearEvents mask = withDisplay $ \d -> io $ do
    Xlib.sync d False
    Xlib.allocaXEvent $ \p -> fix $ \again -> do
        more <- Xlib.checkMaskEvent d mask p
        when more again -- beautiful

-- | tileWindow. Moves and resizes w such that it fits inside the given
-- rectangle, including its border.
tileWindow :: Xlib.Window -> Xlib.Rectangle -> X ()
tileWindow w r = withDisplay $ \d -> withWindowAttributes d w $ \wa -> do
    -- give all windows at least 1x1 pixels
    let bw = fromIntegral $ Xlib.wa_border_width wa
        least x | x <= bw*2  = 1
                | otherwise  = x - bw*2
    io $ Xlib.moveResizeWindow d w (Xlib.rect_x r) (Xlib.rect_y r)
                              (least $ Xlib.rect_width r) (least $ Xlib.rect_height r)

-- ---------------------------------------------------------------------

-- | Returns 'True' if the first rectangle is contained within, but not equal
-- to the second.
containedIn :: Xlib.Rectangle -> Xlib.Rectangle -> Bool
containedIn r1@(Xlib.Rectangle x1 y1 w1 h1) r2@(Xlib.Rectangle x2 y2 w2 h2)
 = and [ r1 /= r2
       , x1 >= x2
       , y1 >= y2
       , fromIntegral x1 + w1 <= fromIntegral x2 + w2
       , fromIntegral y1 + h1 <= fromIntegral y2 + h2 ]

-- | Given a list of screens, remove all duplicated screens and screens that
-- are entirely contained within another.
nubScreens :: [Xlib.Rectangle] -> [Xlib.Rectangle]
nubScreens xs = nub . filter (\x -> not $ any (x `containedIn`) xs) $ xs

-- | Cleans the list of screens according to the rules documented for
-- nubScreens.
getCleanedScreenInfo :: MonadIO m => Xlib.Display -> m [Xlib.Rectangle]
getCleanedScreenInfo = io .  fmap nubScreens . Xlib.getScreenInfo

-- | rescreen.  The screen configuration may have changed (due to
-- xrandr), update the state and refresh the screen, and reset the gap.
rescreen :: X ()
rescreen = do
    xinesc <- withDisplay getCleanedScreenInfo

    windows $ \ws@(W.StackSet { W.current = v, W.visible = vs, W.hidden = hs }) ->
        let (xs, ys) = splitAt (length xinesc) $ map W.workspace (v:vs) ++ hs
            (a:as)   = zipWith3 W.Screen xs [0..] $ map SD xinesc
        in  ws { W.current = a
               , W.visible = as
               , W.hidden  = ys }

-- ---------------------------------------------------------------------

-- | setButtonGrab. Tell whether or not to intercept clicks on a given window
setButtonGrab :: Bool -> Xlib.Window -> X ()
setButtonGrab grab w = do
    pointerMode <- asks $ \c -> if clickJustFocuses (config c)
                                    then Xlib.grabModeAsync
                                    else Xlib.grabModeSync
    withDisplay $ \d -> io $ if grab
        then forM_ [Xlib.button1, Xlib.button2, Xlib.button3] $ \b ->
            Xlib.grabButton d b Xlib.anyModifier w False Xlib.buttonPressMask
                       pointerMode Xlib.grabModeSync Xlib.none Xlib.none
        else Xlib.ungrabButton d Xlib.anyButton Xlib.anyModifier w

-- ---------------------------------------------------------------------
-- Setting keyboard focus

-- | Set the focus to the window on top of the stack, or root
setTopFocus :: X ()
setTopFocus = withWindowSet $ maybe (setFocusX =<< asks theRoot) setFocusX . W.peek

-- | Set focus explicitly to window 'w' if it is managed by us, or root.
-- This happens if X notices we've moved the mouse (and perhaps moved
-- the mouse to a new screen).
focus :: Xlib.Window -> X ()
focus w = local (\c -> c { mouseFocused = True }) $ withWindowSet $ \s -> do
    let stag = W.tag . W.workspace
        curr = stag $ W.current s
    mnew <- maybe (return Nothing) (fmap (fmap stag) . uncurry pointScreen)
            =<< asks mousePosition
    root <- asks theRoot
    case () of
        _ | W.member w s && W.peek s /= Just w -> windows (W.focusWindow w)
          | Just new <- mnew, w == root && curr /= new
                                               -> windows (W.view new)
          | otherwise                          -> return ()

-- | Call X to set the keyboard focus details.
setFocusX :: Xlib.Window -> X ()
setFocusX w = withWindowSet $ \ws -> do
    dpy <- asks display

    -- clear mouse button grab and border on other windows
    forM_ (W.current ws : W.visible ws) $ \wk ->
        forM_ (W.index (W.view (W.tag (W.workspace wk)) ws)) $ \otherw ->
            setButtonGrab True otherw

    -- If we ungrab buttons on the root window, we lose our mouse bindings.
    whenX (not <$> isRoot w) $ setButtonGrab False w

    hints <- io $ Xlib.getWMHints dpy w
    protocols <- io $ Xlib.getWMProtocols dpy w
    wmprot <- atom_WM_PROTOCOLS
    wmtf <- atom_WM_TAKE_FOCUS
    currevt <- asks currentEvent
    let inputHintSet = Xlib.wmh_flags hints `testBit` Xlib.inputHintBit

    when ((inputHintSet && Xlib.wmh_input hints) || (not inputHintSet)) $
      io $ do Xlib.setInputFocus dpy w Xlib.revertToPointerRoot 0
    when (wmtf `elem` protocols) $
      io $ Xlib.allocaXEvent $ \ev -> do
        Xlib.setEventType ev Xlib.clientMessage
        Xlib.setClientMessageEvent ev w wmprot 32 wmtf $ maybe Xlib.currentTime event_time currevt
        Xlib.sendEvent dpy w False Xlib.noEventMask ev
        where event_time ev =
                if (Xlib.ev_event_type ev) `elem` timedEvents then
                  Xlib.ev_time ev
                else
                  Xlib.currentTime
              timedEvents = [ Xlib.keyPress, Xlib.keyRelease, Xlib.buttonPress, Xlib.buttonRelease, Xlib.enterNotify, Xlib.leaveNotify, Xlib.selectionRequest ]

------------------------------------------------------------------------
-- Message handling

-- | Throw a message to the current 'LayoutClass' possibly modifying how we
-- layout the windows, in which case changes are handled through a refresh.
sendMessage :: Message a => a -> X ()
sendMessage a = windowBracket_ $ do
    w <- W.workspace . W.current <$> gets windowset
    ml' <- handleMessage (W.layout w) (SomeMessage a) `catchX` return Nothing
    whenJust ml' $ \l' ->
        modifyWindowSet $ \ws -> ws { W.current = (W.current ws)
                                { W.workspace = (W.workspace $ W.current ws)
                                  { W.layout = l' }}}
    return (Any $ isJust ml')

-- | Send a message to all layouts, without refreshing.
broadcastMessage :: Message a => a -> X ()
broadcastMessage a = withWindowSet $ \ws -> do
   let c = W.workspace . W.current $ ws
       v = map W.workspace . W.visible $ ws
       h = W.hidden ws
   mapM_ (sendMessageWithNoRefresh a) (c : v ++ h)

-- | Send a message to a layout, without refreshing.
sendMessageWithNoRefresh :: Message a => a -> W.Workspace WorkspaceId (Layout Xlib.Window) Xlib.Window -> X ()
sendMessageWithNoRefresh a w =
    handleMessage (W.layout w) (SomeMessage a) `catchX` return Nothing >>=
    updateLayout  (W.tag w)

-- | Update the layout field of a workspace
updateLayout :: WorkspaceId -> Maybe (Layout Xlib.Window) -> X ()
updateLayout i ml = whenJust ml $ \l ->
    runOnWorkspaces $ \ww -> return $ if W.tag ww == i then ww { W.layout = l} else ww

-- | Set the layout of the currently viewed workspace
setLayout :: Layout Xlib.Window -> X ()
setLayout l = do
    ss@(W.StackSet { W.current = c@(W.Screen { W.workspace = ws })}) <- gets windowset
    handleMessage (W.layout ws) (SomeMessage ReleaseResources)
    windows $ const $ ss {W.current = c { W.workspace = ws { W.layout = l } } }

------------------------------------------------------------------------
-- Utilities

-- | Return workspace visible on screen 'sc', or 'Nothing'.
screenWorkspace :: ScreenId -> X (Maybe WorkspaceId)
screenWorkspace sc = withWindowSet $ return . W.lookupWorkspace sc

-- | Apply an 'X' operation to the currently focused window, if there is one.
withFocused :: (Xlib.Window -> X ()) -> X ()
withFocused f = withWindowSet $ \w -> whenJust (W.peek w) f

-- | 'True' if window is under management by us
isClient :: Xlib.Window -> X Bool
isClient w = withWindowSet $ return . W.member w

-- | Combinations of extra modifier masks we need to grab keys\/buttons for.
-- (numlock and capslock)
extraModifiers :: X [Xlib.KeyMask]
extraModifiers = do
    nlm <- gets numberlockMask
    return [0, nlm, Xlib.lockMask, nlm .|. Xlib.lockMask ]

-- | Strip numlock\/capslock from a mask
cleanMask :: Xlib.KeyMask -> X Xlib.KeyMask
cleanMask km = do
    nlm <- gets numberlockMask
    return (complement (nlm .|. Xlib.lockMask) .&. km)

-- | Get the 'Pixel' value for a named color
initColor :: Xlib.Display -> String -> IO (Maybe Xlib.Pixel)
initColor dpy c = C.handle (\(C.SomeException _) -> return Nothing) $
    (Just . Xlib.color_pixel . fst) <$> Xlib.allocNamedColor dpy colormap c
    where colormap = Xlib.defaultColormap dpy (Xlib.defaultScreen dpy)

------------------------------------------------------------------------

-- | A type to help serialize xmonad's state to a file.
data StateFile = StateFile
  { sfWins :: W.StackSet  WorkspaceId String Xlib.Window ScreenId ScreenDetail
  , sfExt  :: [(String, String)]
  } deriving (Show, Read)

-- | Write the current window state (and extensible state) to a file
-- so that xmonad can resume with that state intact.
writeStateToFile :: X ()
writeStateToFile = do
    let maybeShow (t, Right (PersistentExtension ext)) = Just (t, show ext)
        maybeShow (t, Left str) = Just (t, str)
        maybeShow _ = Nothing

        wsData   = W.mapLayout show . windowset
        extState = catMaybes . map maybeShow . M.toList . extensibleState

    path  <- stateFileName
    stateData <- gets (\s -> StateFile (wsData s) (extState s))
    catchIO (writeFile path $ show stateData)

-- | Read the state of a previous xmonad instance from a file and
-- return that state.  The state file is removed after reading it.
readStateFile :: (LayoutClass l Xlib.Window, Read (l Xlib.Window)) => XConfig l -> X (Maybe XState)
readStateFile xmc = do
    path <- stateFileName

    -- I'm trying really hard here to make sure we read the entire
    -- contents of the file before it is removed from the file system.
    sf' <- userCode . io $ do
        raw <- withFile path ReadMode readStrict
        return $! maybeRead reads raw

    io (removeFile path)

    return $ do
      sf <- join sf'

      let winset = W.ensureTags layout (workspaces xmc) $ W.mapLayout (fromMaybe layout . maybeRead lreads) (sfWins sf)
          extState = M.fromList . map (second Left) $ sfExt sf

      return XState { windowset       = winset
                    , numberlockMask  = 0
                    , mapped          = S.empty
                    , waitingUnmap    = M.empty
                    , dragging        = Nothing
                    , extensibleState = extState
                    }
  where
    layout = Layout (layoutHook xmc)
    lreads = readsLayout layout
    maybeRead reads' s = case reads' s of
                           [(x, "")] -> Just x
                           _         -> Nothing

    readStrict :: Handle -> IO String
    readStrict h = hGetContents h >>= \s -> length s `seq` return s

-- | Migrate state from a previously running xmonad instance that used
-- the older @--resume@ technique.
{-# DEPRECATED migrateState "will be removed some point in the future." #-}
migrateState :: (Functor m, MonadIO m) => String -> String -> m ()
migrateState ws xs = do
    io (putStrLn "WARNING: --resume is no longer supported.")
    whenJust stateData $ \s -> do
      path <- stateFileName
      catchIO (writeFile path $ show s)
  where
    stateData = StateFile <$> maybeRead ws <*> maybeRead xs
    maybeRead s = case reads s of
                    [(x, "")] -> Just x
                    _         -> Nothing

-- | @restart name resume@. Attempt to restart xmonad by executing the program
-- @name@.  If @resume@ is 'True', restart with the current window state.
-- When executing another window manager, @resume@ should be 'False'.
restart :: String -> Bool -> X ()
restart prog resume = do
    broadcastMessage ReleaseResources
    io . Xlib.flush =<< asks display
    when resume writeStateToFile
    catchIO (executeFile prog True [] Nothing)

------------------------------------------------------------------------
-- | Floating layer support

-- | Given a window, find the screen it is located on, and compute
-- the geometry of that window wrt. that screen.
floatLocation :: Xlib.Window -> X (ScreenId, W.RationalRect)
floatLocation w =
    catchX go $ do
      -- Fallback solution if `go' fails.  Which it might, since it
      -- calls `getWindowAttributes'.
      sc <- W.current <$> gets windowset
      return (W.screen sc, W.RationalRect 0 0 1 1)

  where fi x = fromIntegral x
        go = withDisplay $ \d -> do
          ws <- gets windowset
          wa <- io $ Xlib.getWindowAttributes d w
          let bw = (fromIntegral . Xlib.wa_border_width) wa
          sc <- fromMaybe (W.current ws) <$> pointScreen (fi $ Xlib.wa_x wa) (fi $ Xlib.wa_y wa)

          let sr = screenRect . W.screenDetail $ sc
              rr = W.RationalRect ((fi (Xlib.wa_x wa) - fi (Xlib.rect_x sr)) % fi (Xlib.rect_width sr))
                                  ((fi (Xlib.wa_y wa) - fi (Xlib.rect_y sr)) % fi (Xlib.rect_height sr))
                                  (fi (Xlib.wa_width  wa + bw*2) % fi (Xlib.rect_width sr))
                                  (fi (Xlib.wa_height wa + bw*2) % fi (Xlib.rect_height sr))

          return (W.screen sc, rr)

-- | Given a point, determine the screen (if any) that contains it.
pointScreen :: Xlib.Position -> Xlib.Position
            -> X (Maybe (W.Screen WorkspaceId (Layout Xlib.Window) Xlib.Window ScreenId ScreenDetail))
pointScreen x y = withWindowSet $ return . find p . W.screens
  where p = pointWithin x y . screenRect . W.screenDetail

-- | @pointWithin x y r@ returns 'True' if the @(x, y)@ co-ordinate is within
-- @r@.
pointWithin :: Xlib.Position -> Xlib.Position -> Xlib.Rectangle -> Bool
pointWithin x y r = x >= Xlib.rect_x r &&
                    x <  Xlib.rect_x r + fromIntegral (Xlib.rect_width r) &&
                    y >= Xlib.rect_y r &&
                    y <  Xlib.rect_y r + fromIntegral (Xlib.rect_height r)

-- | Make a tiled window floating, using its suggested rectangle
float :: Xlib.Window -> X ()
float w = do
    (sc, rr) <- floatLocation w
    windows $ \ws -> W.float w rr . fromMaybe ws $ do
        i  <- W.findTag w ws
        guard $ i `elem` map (W.tag . W.workspace) (W.screens ws)
        f  <- W.peek ws
        sw <- W.lookupWorkspace sc ws
        return (W.focusWindow f . W.shiftWin sw w $ ws)

-- ---------------------------------------------------------------------
-- Mouse handling

-- | Accumulate mouse motion events
mouseDrag :: (Xlib.Position -> Xlib.Position -> X ()) -> X () -> X ()
mouseDrag f done = do
    drag <- gets dragging
    case drag of
        Just _ -> return () -- error case? we're already dragging
        Nothing -> do
            XConf { theRoot = root, display = d } <- ask
            io $ Xlib.grabPointer d root False (Xlib.buttonReleaseMask .|. Xlib.pointerMotionMask)
                    Xlib.grabModeAsync Xlib.grabModeAsync Xlib.none Xlib.none Xlib.currentTime
            modify $ \s -> s { dragging = Just (motion, cleanup) }
 where
    cleanup = do
        withDisplay $ io . flip Xlib.ungrabPointer Xlib.currentTime
        modify $ \s -> s { dragging = Nothing }
        done
    motion x y = do z <- f x y
                    clearEvents Xlib.pointerMotionMask
                    return z

-- | drag the window under the cursor with the mouse while it is dragged
mouseMoveWindow :: Xlib.Window -> X ()
mouseMoveWindow w = whenX (isClient w) $ withDisplay $ \d -> do
    io $ Xlib.raiseWindow d w
    wa <- io $ Xlib.getWindowAttributes d w
    (_, _, _, ox', oy', _, _, _) <- io $ Xlib.queryPointer d w
    let ox = fromIntegral ox'
        oy = fromIntegral oy'
    mouseDrag (\ex ey -> do
                  io $ Xlib.moveWindow d w (fromIntegral (fromIntegral (Xlib.wa_x wa) + (ex - ox)))
                                      (fromIntegral (fromIntegral (Xlib.wa_y wa) + (ey - oy)))
                  float w
              )
              (float w)

-- | resize the window under the cursor with the mouse while it is dragged
mouseResizeWindow :: Xlib.Window -> X ()
mouseResizeWindow w = whenX (isClient w) $ withDisplay $ \d -> do
    io $ Xlib.raiseWindow d w
    wa <- io $ Xlib.getWindowAttributes d w
    sh <- io $ Xlib.getWMNormalHints d w
    io $ Xlib.warpPointer d Xlib.none w 0 0 0 0 (fromIntegral (Xlib.wa_width wa)) (fromIntegral (Xlib.wa_height wa))
    mouseDrag (\ex ey -> do
                 io $ Xlib.resizeWindow d w `uncurry`
                    applySizeHintsContents sh (ex - fromIntegral (Xlib.wa_x wa),
                                               ey - fromIntegral (Xlib.wa_y wa))
                 float w)

              (float w)

-- ---------------------------------------------------------------------
-- | Support for window size hints

type D = (Xlib.Dimension, Xlib.Dimension)

-- | Given a window, build an adjuster function that will reduce the given
-- dimensions according to the window's border width and size hints.
mkAdjust :: Xlib.Window -> X (D -> D)
mkAdjust w = withDisplay $ \d -> liftIO $ do
    sh <- Xlib.getWMNormalHints d w
    wa <- C.try $ Xlib.getWindowAttributes d w
    case wa of
         Left  err -> const (return id) (err :: C.SomeException)
         Right wa' ->
            let bw = fromIntegral $ Xlib.wa_border_width wa'
            in  return $ applySizeHints bw sh

-- | Reduce the dimensions if needed to comply to the given SizeHints, taking
-- window borders into account.
applySizeHints :: Integral a => Xlib.Dimension -> Xlib.SizeHints -> (a, a) -> D
applySizeHints bw sh =
    tmap (+ 2 * bw) . applySizeHintsContents sh . tmap (subtract $ 2 * fromIntegral bw)
    where
    tmap f (x, y) = (f x, f y)

-- | Reduce the dimensions if needed to comply to the given SizeHints.
applySizeHintsContents :: Integral a => Xlib.SizeHints -> (a, a) -> D
applySizeHintsContents sh (w, h) =
    applySizeHints' sh (fromIntegral $ max 1 w, fromIntegral $ max 1 h)

-- | XXX comment me
applySizeHints' :: Xlib.SizeHints -> D -> D
applySizeHints' sh =
      maybe id applyMaxSizeHint                   (Xlib.sh_max_size   sh)
    . maybe id (\(bw, bh) (w, h) -> (w+bw, h+bh)) (Xlib.sh_base_size  sh)
    . maybe id applyResizeIncHint                 (Xlib.sh_resize_inc sh)
    . maybe id applyAspectHint                    (Xlib.sh_aspect     sh)
    . maybe id (\(bw,bh) (w,h)   -> (w-bw, h-bh)) (Xlib.sh_base_size  sh)

-- | Reduce the dimensions so their aspect ratio falls between the two given aspect ratios.
applyAspectHint :: (D, D) -> D -> D
applyAspectHint ((minx, miny), (maxx, maxy)) x@(w,h)
    | or [minx < 1, miny < 1, maxx < 1, maxy < 1] = x
    | w * maxy > h * maxx                         = (h * maxx `div` maxy, h)
    | w * miny < h * minx                         = (w, w * miny `div` minx)
    | otherwise                                   = x

-- | Reduce the dimensions so they are a multiple of the size increments.
applyResizeIncHint :: D -> D -> D
applyResizeIncHint (iw,ih) x@(w,h) =
    if iw > 0 && ih > 0 then (w - w `mod` iw, h - h `mod` ih) else x

-- | Reduce the dimensions if they exceed the given maximum dimensions.
applyMaxSizeHint  :: D -> D -> D
applyMaxSizeHint (mw,mh) x@(w,h) =
    if mw > 0 && mh > 0 then (min w mw,min h mh) else x
