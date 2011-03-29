{-# LANGUAGE TupleSections #-}

import Data.List
import Data.Maybe
import Data.Monoid
import Control.Applicative
import Control.Monad
import Data.Array
import Data.MemoTrie (memo)
import Data.Graph.Inductive
import Data.GraphViz
import System.IO.Unsafe
import Control.Monad.ST
import Data.STRef

data Var = Var { varName :: String, varEvents :: Int } deriving (Eq, Ord)

data Ev = Ev { eventVar :: Var, eventIndex :: Int } deriving (Eq, Ord)

data Fac = Fac { facScope :: [Var], facFun :: [Int] -> Double }

instance Show Var where
  show (Var name n) = name -- ++ "#" ++ show n

instance Show Ev where
  show (Ev (Var name _) i) = name ++ show i

instance Show Fac where
  show (Fac scope _) = name -- ++ "=" ++ show rules
    where name = "φ(" ++ let s = show scope in drop 1 $ take (length s - 1) s ++ ")"

instance Monoid Fac where
  mempty = unitFac
  mappend = (|*|)

binVar :: String -> Var
binVar s = Var s 2

unitFac :: Fac
unitFac = Fac [] (\[] -> 1.0)

facProb :: Fac -> Double
facProb (Fac [] fn) = fn []

showTable :: Fac -> String
showTable (Fac vs fn) =
  let
    events (Var _ n) = reverse [0..n-1]
    header = intercalate "\t" $ map varName vs
    row args = intercalate "\t" $ (map show args) ++ [show $ fn args]
    rows = intercalate "\n" $ map row (sequence $ map events vs)
  in
    "\n" ++ header ++ "\n" ++ rows ++ "\n"

memoFac :: Fac -> Fac
memoFac (Fac vs fn) = Fac vs $ memo fn

(|*|) :: Fac -> Fac -> Fac
f1@(Fac vs1 fn1) |*| f2@(Fac vs2 fn2) = memoFac $ Fac newVs newFn
  where
    newVs = nub $ vs1 ++ vs2
    newFn es = p f1 * p f2
      where
        p :: Fac -> Double
        p (Fac vs fn) = fn (transform newVs vs es)
        
-- This seems like a generally pretty useful function
transform :: Eq a => [a] -> [a] -> [b] -> [b]
transform as1 as2 bs = result
  where
    idxMap = map (flip elemIndex as2) as1
    indexedResults = [(i, b) | (maybeI, b) <- zip idxMap bs, i <- maybeToList maybeI]
    result = map snd $ sortBy (\(x, _)(y, _) -> x `compare` y) indexedResults

zipIndex :: [a] -> [(Int, a)]
zipIndex = zip [0..]

multAll :: [Fac] -> Fac
multAll = mconcat

sumOut :: Var -> Fac -> Fac
sumOut v@(Var _ n) f@(Fac vs fn) = memoFac $ Fac newVs newFn
  where
    newVs = delete v vs
    insert e es i = fn $ insertAt i es e
    newFn es = sum [fromMaybe (fn es) $ fmap (insert e es) $ elemIndex v vs | e <- [0..n-1]]

-- Another useful general-purpose function
insertAt :: Int -> [a] -> a -> [a] 
insertAt idx es e = before ++ (e : after)
  where
    (before, after) = splitAt idx es

sumOutAll :: [Var] -> Fac -> Fac
sumOutAll [] fac = fac
sumOutAll (v:vs) fac = sumOut v $ sumOutAll vs fac

indicate :: Ev -> Fac
indicate (Ev v n) = Fac [v] fn where
  fn [x] | x == n    = 1
         | otherwise = 0

reduce :: [Ev] -> Fac -> Fac
reduce [] = id
reduce (e:es) = memoFac . reduce es . sumOut (eventVar e) . (indicate e |*|)

naiveQuery :: [Ev] -> [Ev] -> [Var] -> [Fac] -> Double
naiveQuery outcome evidence vars = (/) <$> rawProb (outcome ++ evidence) vars <*> rawProb evidence vars

elimCond :: [Var] -> [Ev] -> [Fac] -> [Fac]
elimCond vs es fs = elim vs $ map (reduce es) fs

rawProb :: [Ev] -> [Var] -> [Fac] -> Double
rawProb es vs = (\f -> f []) . facFun . sumOutAll (vs \\ map eventVar es) . multAll . map (reduce es)

elim :: [Var] -> [Fac] -> [Fac]
elim []     fs = fs
elim (v:vs) fs =
  let (matches, nonMatches) = partition (any(==v) . facScope) fs
      newFactor = sumOut v $ multAll matches
  in 
      elim vs (newFactor : nonMatches)

elimQuery :: [Ev] -> [Ev] -> [Var] -> [Fac] -> Double
elimQuery query obs allVars facs =
  let queryVars = map eventVar query
      auxVars = allVars \\ (queryVars ++ map eventVar obs)
      f = multAll $ elimCond auxVars obs facs
      num = facProb $ reduce query f
      denom = facProb $ sumOutAll queryVars f
  in num / denom

-- Normalize a distribution... only makes sense on factors which are distributions
norm :: Fac -> Fac
norm fac@(Fac vs fn) = Fac vs newFn
  where
    z = facProb $ sumOutAll vs fac
    newFn es = fn es / z

(|/|) :: Fac -> Fac -> Fac
(Fac vs1 fn1) |/| (Fac vs2 fn2) = memoFac $ Fac vs1 newFn
  where
    -- special division: 0/0 = 0
    0 // 0 = 0
    x // y = x / y
    
    newFn es = fn1 es // fn2 (transform vs1 vs2 es)

-- Same as regular groupBy, but sorts first so that all things which satisfy the predicate are combined
groupBy' :: Ord a => (a -> a -> Bool) -> [a] -> [[a]]
groupBy' belongsWith = groupBy belongsWith . sortBy ord
  where ord x y = if x `belongsWith` y then EQ else x `compare` y

-- Order based on locations in a list
listOrd :: Eq a => [a] -> (a -> a -> Ordering)
listOrd as a1 a2 = compare <$> (elemIndex a1) <*> (elemIndex a2) $ as

-- Bayesian or Markov network
type PGraph = Gr Var ()

-- Cluster graph
type CGraph = Gr [Var] ()

-- Belief graph
type BGraph = Gr Fac Fac

-- Find all variables referenced by a set of factors
allVars :: [Fac] -> [Var]
allVars = nub . join . map facScope

-- Constructs a markov network from a set of factors
buildMarkov :: [Fac] -> PGraph
buildMarkov facs = 
  let nodes = zip [1..] $ allVars facs
      findNode v = fst $ fromJust $ find ((v==).snd) nodes
      edges = [(findNode v1, findNode v2, ()) | f <- facs, let s = facScope f, v1 <- s, v2 <- s, v1 /= v2]
  in mkGraph nodes edges
       
p s x = unsafePerformIO $ do { putStrLn $ s; return x }

-- Build a clique tree via variable elimination
buildCTree :: (Var -> Var -> Ordering) -> [Fac] -> CGraph
buildCTree ord facs = nubEdges $ merge 0 (noNodes graph) graph 
  where
    graph = undir $ mkGraph allNodes allEdges
    (allNodes, allEdges) = build 0 (sortBy ord $ allVars facs) (facs `zip` repeat Nothing)
    nubEdges g = mkGraph (labNodes g) (nub $ labEdges g)
    build :: Int -> [Var] -> [(Fac, Maybe Int)] -> ([LNode [Var]], [LEdge ()])
    build _ [] _ = ([], [])
    build n (v:vs) facs = (newNode : nodes, newEdges ++ edges)
      where
        (matches, nonMatches) = partition (any(==v) . facScope . fst) facs
        newFactor = sumOut v $ multAll (map fst matches)
        contribs = matches >>= (maybeToList . snd)
        newEdges = (zip3 contribs (repeat n) (repeat ()))
        nodeVars = nub $ matches >>= (facScope . fst)
        newNode = (n, nodeVars)
        (nodes, edges) = build (n+1) vs ((newFactor, Just n) : nonMatches)
    -- Merge all non-maximal cliques into their maximal counterparts
    merge :: Node -> Int -> CGraph -> CGraph
    merge n mx g | n >= mx   = g
                 | otherwise = newG
      where
        vars = fromJust . lab g
        nbs = neighbors g n
        dominator = find (null . (vars n \\) . vars) nbs
        newG = merge (n+1) mx $ case dominator of
          Nothing -> g
          Just d -> insEdges (map (\(x, y) -> (x, y, ())) newEdges) newG'
            where
              newG' = delNode n g
              existing = edges newG'
              newEdges = nbs >>= \nb -> if nb == d then [] else [(nb, d), (d, nb)]
              
type STFac s = STRef s Fac
              
-- Create initial beliefs: each cluster has its assigned factors multiplied together; 
-- the sepsets contain no information
beliefInit :: [Fac] -> CGraph -> BGraph
beliefInit fs g = emap (const unitFac) $ nmap multAll $ assign fs g

unlabelEdges :: LEdge a -> Edge
unlabelEdges (n, m, a) = (n, m)

unlabelNodes :: LNode a -> Node
unlabelNodes (n, a) = n

revEdge :: LEdge a -> LEdge a
revEdge (n, m, a) = (m, n, a)

changeNode :: DynGraph g => (a -> a) -> Node -> g a b -> g a b
changeNode f n g = result
  where
    (ctx, g') = match n g
    result = case ctx of
      Nothing -> g
      Just (is, n, a, os) -> (is, n, f a, os) & g'

compose :: [a -> a] -> a -> a
compose [] = id
compose (f:fs) = f . compose fs

beliefUpdate :: Node -> BGraph -> BGraph
beliefUpdate n g = emap norm $ nmap norm $ compose nodeChanges g'
  where
    es = out g n
    lab' = fromJust . lab g
    es' = map (\(n, m, f) -> (n, m, sumOutAll (nodeVars n \\ nodeVars m) $ lab' n)) es
    nodeVars = facScope . lab'
    g' = insEdges (es' ++ map revEdge es') $ delEdges (map unlabelEdges (es ++ map revEdge es)) g
    nbs :: [LNode Fac]
    nbs = map (\(nb,oldMsg,newMsg) -> (nb, lab' nb |*| (newMsg |/| oldMsg))) $ zipWith (\(_,nb,a)(_,_,b) -> (nb,a,b)) es es'
    nodeChanges :: [BGraph -> BGraph]
    nodeChanges = map (\(n, f) -> changeNode (const f) n) nbs

decomp :: Gr a b -> [Context a b]
decomp g | isEmpty g = []
         | otherwise = let (ctx, g') = matchAny g in ctx : decomp g'

assign :: [Fac] -> CGraph -> Gr [Fac] ()
assign facs g = mkGraph ns es
  where
    assign' :: [Fac] -> [(Int, ([Fac], [Var]))] -> [(Int, ([Fac], [Var]))]
    assign' [] ns = ns 
    assign' (f@(Fac vs _):fs) ns = assign' fs $ map (\old@(n, (fs', vs')) -> if (null (vs \\ vs')) then (n, (f:fs', vs')) else old) ns
    ns = map (\(n, (fs, vs)) -> (n, fs)) $ assign' facs (map (\(n, vs) -> (n, ([], vs))) $ labNodes g)
    es = labEdges g

beliefUpdateAll :: BGraph -> BGraph
beliefUpdateAll g = compose (map beliefUpdate $ nodes g) g

example :: BGraph
example = beliefInit burgleFacs $ buildCTree (listOrd [vB,vPGH,vA,vE,vR,vM]) (map (reduce [Ev vJ 1]) burgleFacs)

main = viz example
--main = viz $ buildCTree (listOrd [vB,vPGH,vA,vE,vJ,vR,vM]) burgleFacs

viz :: Gr Fac Fac -> IO ()
viz graph =
  let path = "test"
      format = Png
      params = nonClusteredParams { globalAttributes = [] --[GraphAttrs [Size $ createPoint 1000 1000]]
                             --, clusterBy        = \node@(n,lbl) -> if (n > 1) then C True $ N node else N node
                             --, fmtCluster       = const [GraphAttrs [BgColor $ RGB 0 255 150], NodeAttrs [Shape DoubleCircle]]
                             , fmtEdge          = \(_,_,lbl) -> [Label (StrLabel lbl)] 
                             , fmtNode          = \(_,lbl)   -> [Label (StrLabel lbl)]
                             }
      command = Fdp
      --graph = vor
      graph' :: Gr String String
      graph' = nmap showTable $ emap showTable $ graph --buildMarkov burgleFacs
  in do
    --putStrLn $ show $ edges graph
    Right path <- addExtension (runGraphvizCommand command (setDirectedness graphToDot params graph')) format path
    putStrLn path

-- Burglary/Earthquake Example for HW4
vB   = binVar "B" 
vE   = binVar "E"
vA   = binVar "A"
vJ   = binVar "J"
vM   = binVar "M"
vR   = binVar "R"
vPGH = binVar "PGH"

foo x = g x
  where
    g x = x * 2

fB :: Fac
fB = Fac [vB] f where 
  f es = case es of
    [1] -> 0.001
    [0] -> 1 - f[1]

fE = Fac [vE] f where 
  f es = case es of
    [1] -> 0.002
    [0] -> 1 - f[1]

fA_BE = Fac [vA, vB, vE] f where
  f es = case es of
    [1,1,1] -> 0.95
    [1,1,0] -> 0.94
    [1,0,1] -> 0.29
    [1,0,0] -> 0.001
    [0,b,e] -> 1 - f[1,b,e]

fM_A = Fac [vM, vA] f where 
  f es = case es of
    [1,1] -> 0.7
    [1,0] -> 0.01
    [0,a] -> 1 - f[1,a]
     
fJ_A = Fac [vJ, vA] f where
  f es = case es of
    [1,1] -> 0.9
    [1,0] -> 0.05
    [0,a] -> 1 - f[1,a]

fR_E = Fac [vR, vE] f where
  f es = case es of
    [1,1] -> 0.9
    [1,0] -> 0.1
    [0,e] -> 1 - f[1,e]

fPGH_JMR = Fac [vPGH, vJ, vM, vR] f where
  f es = case es of
    [1,1,1,1] -> 0.99
    [1,1,1,0] -> 0.7
    [1,1,0,1] -> 0.85
    [1,1,0,0] -> 0.60
    [1,0,1,1] -> 0.95
    [1,0,1,0] -> 0.50
    [1,0,0,1] -> 0.90
    [1,0,0,0] -> 0.001
    [0,j,m,r] -> 1 - f[1,j,m,r]

burgleVars :: [Var]
burgleVars = [vB, vE, vA, vM, vJ, vR, vPGH]

burgleFacs :: [Fac]
burgleFacs = [fB, fE, fA_BE, fJ_A, fM_A, fR_E, fPGH_JMR]

putTable name fac = putStrLn $ name ++ ":" ++ showTable fac

hw4_c_and_d = 
  do
    putStrLn "Part (c)\n"
    putStrLn "Calculate the initial potentials...\n"
    putTable "ψ1(B,E,A) = φ(B)φ(B,E,A)" ψ1
    putTable "ψ2(E,R) = φ(E)φ(E,R)" ψ2
    putTable "ψ3(A,M) = φ(A,j1)φ(A,M)" ψ3
    putTable "ψ4(M,R,PGH) = φ(j1,M,R,PGH)" ψ4
    
    putStrLn "Calculate the messages...\n"
    putTable "δ1→2(E,A) = ΣB ψ1"     δ1_2 
    putTable "δ2→3(A,R) = ΣE ψ2 δ1→2" δ2_3
    putTable "δ3→4(R,M) = ΣA ψ3 δ2→3" δ3_4
    putTable "δ4→3(R,M) = ΣPGH ψ4"   δ4_3
    putTable "δ3→2(A,R) = ΣM ψ3 δ4→3" δ3_2
    putTable "δ2→1(E,A) = ΣR ψ2 δ3→2" δ2_1
    
    putStrLn "Calculate the relevant clique beliefs...\n"
    putTable "β1(B,E,A) = ψ1 δ2→1" β1
    putTable "β4(M,R,PGH) = ψ4 δ3→4" β4

    putStrLn "Finally calculate the probability distributions for the target variables...\n"
    putTable "x(B,E) = norm(ΣA β1)" x
    putTable "P(B) = ΣE x" pB
    putTable "P(E) = ΣB x" pE
    
    putTable "P(PGH) = norm(ΣR ΣM β4)" pPGH
  
    putStrLn "Part (d)\n"
    putStrLn "First we indicate R=r0 to C4, thus generating a new belief β4'.\n"
    putTable "β4' = β4[R=r0]" β4'
    putStrLn "From this we can immediately calculate the new distribution P'(PGH).\n"
    putTable "P'(PGH) = norm(ΣR ΣM β4')" pPGH'
    putStrLn 
      "To calculate the updated distributions P'(B) and P'(E) we need to propagate a message back from C4 to C1.\n"
    
    putTable "ψ4' = β4' / δ3_4" ψ4'
    putTable "δ4→3'(R,M) = ΣPGH ψ4'" δ4_3'
    putTable "δ3→2'(A,R) = ΣM ψ3 δ4→3'" δ3_2'
    putTable "δ2→1'(E,A) = ΣR ψ2 δ3→2'" δ2_1'

    putTable "β1'(B,E,A) = ψ1 δ2→1'" β1'
    putTable "x'(B,E) = norm(ΣA β1')" x'
    putTable "P'(B) = ΣE x'" pB'
    putTable "P'(E) = ΣB x'" pE'
                
  where
    
    -- Part (c)
    
    j1 = Ev vJ 1
    b1 = Ev vB 1
    r0 = Ev vR 0
    
    ψ1 = fB |*| fA_BE
    ψ2 = fE |*| fR_E
    ψ3 = reduce [j1] fJ_A |*| fM_A
    ψ4 = reduce [j1] fPGH_JMR

    δ1_2 = sumOut vB ψ1
    δ2_3 = sumOut vE $ ψ2 |*| δ1_2
    δ3_4 = sumOut vA $ ψ3 |*| δ2_3
    δ4_3 = sumOut vPGH ψ4
    δ3_2 = sumOut vM $ ψ3 |*| δ4_3
    δ2_1 = sumOut vR $ ψ2 |*| δ3_2
    
    β1 = ψ1 |*| δ2_1
    β4 = ψ4 |*| δ3_4
    
    x = norm $ sumOut vA β1
    pB = sumOut vE x
    pE = sumOut vB x
    pPGH = norm $ sumOutAll [vM, vR] β4
    
    -- Part (d)
    
    β4' = indicate r0 |*| β4
    pPGH' = norm $ sumOutAll [vM, vR] β4'

    ψ4' = β4' |/| δ3_4
    δ4_3' = sumOut vPGH ψ4'
    δ3_2' = sumOut vM $ ψ3 |*| δ4_3'
    δ2_1' = sumOut vR $ ψ2 |*| δ3_2'
    β1' = ψ1 |*| δ2_1'

    x' = norm $ sumOut vA β1'
    pB' = sumOut vE x'
    pE' = sumOut vB x'
                      
