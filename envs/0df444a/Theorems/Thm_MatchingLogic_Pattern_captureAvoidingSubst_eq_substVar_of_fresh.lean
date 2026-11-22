-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_eq_substVar_of_fresh
-- name    : MatchingLogic.Pattern.captureAvoidingSubst_eq_substVar_of_fresh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:10.243155+00:00
-- url     : https://prove2.me/theorems/58c89e7e-00eb-42d5-87a8-ecfbedf63b1a
-- title:
--   Pattern: capture Avoiding Subst eq subst Var of fresh
-- statement:
--   The Pattern construction uses the capture Avoiding Subst eq subst Var of fresh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L371-L373
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L371-L373

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
open scoped BigOperators

theorem MatchingLogic.Pattern.captureAvoidingSubst_eq_substVar_of_fresh {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) : captureAvoidingSubst x y p = substVar x y p := by sorry
