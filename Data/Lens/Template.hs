{-# LANGUAGE TemplateHaskell, CPP #-}

{- |
This module provides an automatic Template Haskell
routine to scour data type definitions and generate
accessor objects for them automatically.
-}
module Data.Lens.Template (
   nameMakeLenses, makeLenses,
   ) where

import Language.Haskell.TH.Syntax
import Control.Monad (liftM, when)
import Data.Maybe (catMaybes)
import Data.List (nub)
import Data.Lens.Common

-- |@makeLenses n@ where @n@ is the name of a data type
-- declared with @data@ looks through all the declared fields
-- of the data type, and for each field beginning with an underscore
-- generates an accessor of the same name without the underscore.
--
-- It is "nameMakeLenses" n f where @f@ satisfies
--
-- > f ('_' : s) = Just s
-- > f x = Nothing -- otherwise
--
-- For example, given the data type:
--
-- > data Score = Score { 
-- >   _p1Score :: Int
-- > , _p2Score :: Int
-- > , rounds :: Int
-- > }
--
-- @makeLenses@ will generate the following objects:
--
-- > p1Score :: Lens Score Int
-- > p1Score = lens _p1Score (\x s -> s { _p1Score = x })
-- > p2Score :: Lens Score Int
-- > p2Score = lens _p2Score (\x s -> s { _p2Score = x })
--
-- It is used with Template Haskell syntax like:
--
-- > $( makeLenses ''TypeName )
--
-- And will generate accessors when TypeName was declared
-- using @data@ or @newtype@.
makeLenses :: Name -> Q [Dec]
makeLenses n = nameMakeLenses n stripUnderscore

stripUnderscore :: String -> Maybe String
stripUnderscore [] = Nothing
stripUnderscore s 
   | head s == '_' = Just (tail s)
   | otherwise = Nothing

namedFields :: Con -> [VarStrictType]
namedFields (RecC _ fs) = fs
namedFields (ForallC _ _ c) = namedFields c
namedFields _ = []

-- |@nameMakeLenses n f@ where @n@ is the name of a data type
-- declared with @data@ and @f@ is a function from names of fields
-- in that data type to the name of the corresponding accessor. If
-- @f@ returns @Nothing@, then no accessor is generated for that
-- field.
nameMakeLenses :: Name -> (String -> Maybe String) -> Q [Dec]
nameMakeLenses t namer = do
    info <- reify t
    reified <- case info of
                    TyConI dec -> return dec
                    _ -> fail errmsg
    (params, cons) <- case reified of
                 DataD _ _ params cons' _ -> return (params, cons')
                 NewtypeD _ _ params con' _ -> return (params, [con'])
                 _ -> fail errmsg
    decs <- makeAccs params . nub $ concatMap namedFields cons
    when (null decs) $ qReport False nodefmsg
    return decs

    where

    errmsg = "Cannot derive accessors for name " ++ show t ++ " because"
          ++ "\n it is not a type declared with 'data' or 'newtype'"
          ++ "\n Did you remember to double-tick the type as in"
          ++ "\n $(makeLenses ''TheType)?"

    nodefmsg = "Warning: No accessors generated from the name " ++ show t
          ++ "\n If you are using makeLenses rather than"
          ++ "\n nameMakeLenses, remember accessors are"
          ++ "\n only generated for fields ending with an underscore"

    makeAccs :: [TyVarBndr] -> [VarStrictType] -> Q [Dec]
    makeAccs params vars =
        liftM (concat . catMaybes) $ mapM (\ (name,_,ftype) -> makeAccFromName name params ftype) vars

    transformName :: Name -> Maybe Name
    transformName (Name occ f) = do
        n <- namer (occString occ)
        return $ Name (mkOccName n) f

    makeAccFromName :: Name -> [TyVarBndr] -> Type -> Q (Maybe [Dec])
    makeAccFromName name params ftype =
        case transformName name of
            Nothing -> return Nothing
            Just n -> liftM Just $ makeAcc name params ftype n

    -- haddock doesn't grok TH
#ifndef __HADDOCK__

    makeAcc ::Name -> [TyVarBndr] -> Type -> Name -> Q [Dec]
    makeAcc name params ftype accName = do
        let params' = map (\x -> case x of (PlainTV n) -> n; (KindedTV n _) -> n) params
        let appliedT = foldl AppT (ConT t) (map VarT params')
        body <- [|
                 lens
                    ( $( return $ VarE name ) )
                    ( \x s ->
                        $( return $ RecUpdE (VarE 's) [(name, VarE 'x)] ) )
                |]
        return
          [ SigD accName (ForallT (map PlainTV params')
               [] (AppT (AppT (ConT ''Lens) appliedT) ftype))
          , ValD (VarP accName) (NormalB body) []
          ]

#endif
