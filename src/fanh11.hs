import Data.List
import Data.Maybe
import Debug.Trace

data T = App T T
       | If T T T 
       | Succ T
       | Pred T
       | IsZero T
       | Val V
       | Let Label T T
       | Seq T T
       | Alloc T
       | DeRef T
       | Assign T T 
  deriving (Show, Eq)
  
data V = Tru 
        | Fls 
        | Z 
        | SuccNV V 
        | UnitV 
        | Location Loc 
        | Var Label 
        | L Label Type T deriving(Show, Eq)
  
data Label = A | C | D | E | F | G | H | I | J | K 
    | M | O | P | Q | R | S | U | W | X | Y  
    deriving (Show, Eq)
    
data Loc = L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9
    deriving (Show, Eq)

data Type = BOOL | NAT | Unit | Arrow Type Type | Ref Type deriving (Show, Eq)

type Gamma = [(Label, Type)] 

type Mu = [(Loc, V)]

gm :: Gamma
gm = []

mu :: Mu
mu = []

freeVars :: T -> [Label] 
freeVars (Val (Var x)) = [x]
freeVars (Val (L x tp t1)) = res \\ [x] 
        where res = [] ++ freeVars t1
freeVars (App t1 t2) = freeVars t1 `union` freeVars t2

relabel :: T -> Label -> Label -> T 
relabel (Val (Var x)) v1 v2
        |x == v1        = Val (Var v2)
        |otherwise      = Val (Var x)
relabel (Val (L x tp t1)) v1 v2 
        |x == v1        = Val (L v2 tp (relabel t1 v1 v2))
        |otherwise      = Val (L x tp (relabel t1 v1 v2))
relabel (App t1 t2) v1 v2 = App (relabel t1 v1 v2) (relabel t2 v1 v2)

all_labels :: [Label]
all_labels = [A, C, D, E, F, G, H, I, J, K, M, O, P, Q, R, S, U, W, X, Y]

sub_util :: [Label] -> [Label]
sub_util exg_labels = all_labels \\ exg_labels

sub :: T -> Label -> T -> T 
sub (Val (Var v)) x s
        |x == v          = s
        |otherwise       = Val (Var v)

sub (Val (L y tp t1)) x s
        |y == x || length avl_labels == 0   = Val (L y tp t1)
        |not (y `elem` freeVars s)          = Val (L y tp (sub t1 x s))
        |otherwise                          = sub (relabel ((Val (L y tp t1))) y (head avl_labels)) x s
        where avl_labels = sub_util ([x] `union` (freeVars s) `union` (freeVars t1))

sub (App t1 t2) x s = App (sub t1 x s) (sub t2 x s)

isNF :: T -> Bool 
isNF (Val (Var x)) = True
isNF (Val (L x tp t1)) = isNF t1
isNF (App (Val (L x tp t1)) _) = False
isNF (App t1 t2) = isNF t1 && isNF t2

ssos :: (T, Mu) -> (T, Mu)
ssos ((Val (L y tp t1)), mu) = ((Val (L y tp (fst (ssos (t1, mu))))), mu)
ssos (Val v, mu) = (Val v, mu)

ssos ((If (Val Tru) t2 t3), mu) = (t2, mu)
ssos ((If (Val Fls) t2 t3), mu) = (t3, mu)
ssos ((If t1 t2 t3), mu) = ((If (fst (ssos (t1, mu))) t2 t3), mu)

ssos ((Succ (Val nv)), mu) = ((Val (SuccNV nv)), mu)
ssos ((Succ t1), mu) = (Succ (fst (ssos (t1, mu))), mu)

ssos ((Pred (Val Z)), mu) = (Val Z, mu)
ssos ((Pred (Val (SuccNV nv))), mu) = ((Val nv), mu)
ssos ((Pred t1), mu) = (Pred (fst (ssos (t1, mu))), mu)

ssos ((IsZero (Val Z)), mu) = (Val Tru, mu)
ssos ((IsZero (Val (SuccNV nv))), mu) = (Val Fls, mu)
ssos ((IsZero t1), mu) = (IsZero (fst (ssos (t1, mu))), mu)

ssos ((App (Val (L x tp t1)) t2), mu)
        | not (isNF t2)      = ((App (Val (L x tp t1)) (fst (ssos (t2, mu)))), mu)
        | otherwise          = ((sub t1 x t2), mu)
ssos ((App t1 t2), mu)
        | not (isNF t1)      = ((App (fst (ssos (t1, mu))) t2), mu)
        | not (isNF t2)      = ((App t1 (fst (ssos (t2,mu)))), mu)
        | otherwise          = ((App t1 t2), mu)

ssos ((Let x t1 t2), mu)
        | not (isNF t1)      = ((Let x (fst (ssos (t1, mu))) t2), mu)
        | otherwise          = ((sub t2 x t1), mu)

ssos ((Seq (Val UnitV) t2), mu) = (t2, mu)
ssos ((Seq t1 t2), mu) = ((Seq (fst (ssos (t1, mu))) t2), mu)


getType :: Gamma -> Label -> Maybe (Label, Type)
getType gm x
    | null gm               = Nothing
    | fst (head gm) == x    = Just (head gm)
    | otherwise             = getType (tail gm) x

ltInGamma :: Gamma -> (Label, Type) -> Bool
ltInGamma gm (x, tp)
    | null gm       = False
    | fst lt_pair == x && snd lt_pair == tp       = True
    | otherwise     = ltInGamma (tail gm) (x, tp)
    where
        lt_pair = head gm

tcApp :: Maybe Type -> Maybe Type -> Maybe Type
tcApp (Just (Arrow tp11 tp12)) (Just t21)
    | t21 == tp11       = Just tp12
    | otherwise         = Nothing
tcApp _ _       = Nothing 

typeCheck :: Gamma -> T -> Maybe Type
typeCheck gm (Val Tru) = Just BOOL
typeCheck gm (Val Fls) = Just BOOL
typeCheck gm (If t1 t2 t3)
        | t1_type == Just BOOL && t2_type == t3_type      = t2_type
        | otherwise     = Nothing
        where
            t1_type = typeCheck gm t1
            t2_type = typeCheck gm t2 
            t3_type = typeCheck gm t3

typeCheck gm (Val Z) = Just NAT
typeCheck gm (Val (SuccNV v))
        | v == Z || v_type == Just NAT      = Just NAT
        | otherwise     = Nothing
        where
            v_type = typeCheck gm (Val v)
typeCheck gm (Succ t)         
        | typeCheck gm t == Just NAT        = Just NAT
        | otherwise     = Nothing
typeCheck gm (Pred t)
        | typeCheck gm t == Just NAT        = Just NAT
        | otherwise     = Nothing
typeCheck gm (IsZero t)
        | typeCheck gm t == Just NAT        = Just BOOL
        | otherwise     = Nothing

typeCheck gm (Val (Var x))
        | lt_pair /= Nothing        = Just (snd (fromJust lt_pair))
        | otherwise      = Nothing
        where lt_pair = getType gm x

typeCheck gm (Val (L x tp t2))
        | t2_type /= Nothing && inGamma     = Just (Arrow tp (fromJust t2_type))
        | otherwise     = Nothing
        where
            gm' = gm++[(x, tp)]
            t2_type = typeCheck gm' t2
            inGamma = ltInGamma gm' (x, tp)

typeCheck gm (App t1 t2) = tcApp t1_type t2_type
        where
            t1_type = typeCheck gm t1
            t2_type = typeCheck gm t2

typeCheck gm (Val UnitV) = Just Unit

typeCheck gm (Let x t1 t2)
        | t1_type /= Nothing 
            && t2_type /= Nothing 
            && ltInGamma gm (x, fromJust t1_type)       = t2_type
        | otherwise     = Nothing
        where
            t1_type = typeCheck gm t1
            t2_type = typeCheck gm t2

typeCheck gm (Seq t1 t2)
        | t1_type == Just Unit && t2_type /= Nothing    = t2_type
        | otherwise     = Nothing
        where
            t1_type = typeCheck gm t1
            t2_type = typeCheck gm t2


eval :: T -> T 
eval t1
    | t1' == t1     = t1
    | otherwise     = eval t1'
    where 
        t1' = trace ("  |> " ++show t1++"\n  |> memory = " ++show mu++"\n") (fst (ssos (t1, mu)))

run :: T -> T
run t1
    | t1_type /= Nothing    = trace ("Expression Typechecks as : "++show (fromJust t1_type)++"\n") (eval t1)
    | otherwise             = error "Error! Typechecking Failed!"
    where
        t1_type = typeCheck gm t1


