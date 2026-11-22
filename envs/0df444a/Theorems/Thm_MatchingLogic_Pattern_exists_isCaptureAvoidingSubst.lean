-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_exists_isCaptureAvoidingSubst
-- name    : MatchingLogic.Pattern.exists_isCaptureAvoidingSubst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:36.556505+00:00
-- url     : https://prove2.me/theorems/68f8eba8-d8d0-4449-92f3-b4512ea2e18f
-- title:
--   Pattern: exists is Capture Avoiding Subst
-- statement:
--   The Pattern construction uses the exists is Capture Avoiding Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L367-L369
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L367-L369

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

theorem MatchingLogic.Pattern.exists_isCaptureAvoidingSubst (x y : Nat) (p : Pattern S Nat) :
    ∃ q, IsCaptureAvoidingSubst x y p q := by sorry
