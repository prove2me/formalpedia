-- Prove2me | Theorems.Thm_MatchingLogic_Pattern_avoidBinder_eq_self_of_not_mem_allVars
-- name    : MatchingLogic.Pattern.avoidBinder_eq_self_of_not_mem_allVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:35.345983+00:00
-- url     : https://prove2.me/theorems/837060a1-0823-4b4a-be53-b66bbbecdcf9
-- title:
--   Pattern: avoid Binder eq self of not mem all Vars
-- statement:
--   The Pattern construction uses the avoid Binder eq self of not mem all Vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L334-L351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CaptureAvoiding.lean#L334-L351

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

theorem MatchingLogic.Pattern.avoidBinder_eq_self_of_not_mem_allVars {y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) : avoidBinder y p = p := by sorry
