-- Prove2me | Theorems.Thm_MatchingLogic_PForm_subst_liftSignature
-- name    : MatchingLogic.PForm.subst_liftSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:42.265345+00:00
-- url     : https://prove2.me/theorems/cc145118-de1f-4faf-818d-9a8e581eb351
-- title:
--   PForm: subst lift Signature
-- statement:
--   Lifting commutes with propositional-pattern substitution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L174-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/SignatureRestriction.lean#L174-L180

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]

theorem MatchingLogic.PForm.subst_liftSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (p : PForm) (theta : Nat → Pattern (S.restrict F) Var) :
    (p.subst theta).liftSignature F = p.subst (fun n => (theta n).liftSignature F) := by sorry
