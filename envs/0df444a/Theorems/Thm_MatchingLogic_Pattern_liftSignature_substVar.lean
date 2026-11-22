-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_liftSignature_substVar
-- name    : MatchingLogic.Pattern.liftSignature_substVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:41.662542+00:00
-- url     : https://prove2.me/theorems/aadda9c9-4c3d-4004-ab7a-578b0b520ebd
-- title:
--   Pattern: lift Signature subst Var
-- statement:
--   Lifting commutes with the raw variable-for-variable substitution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L91-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L91-L107

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.Pattern

theorem MatchingLogic.Pattern.liftSignature_substVar [DecidableEq S.Sym] (F : Finset S.Sym)
    (x y : Var) (p : Pattern (S.restrict F) Var) :
    (substVar x y p).liftSignature F = substVar x y (p.liftSignature F) := by sorry
