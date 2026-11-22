-- Prove2me | Theorems.Thm_MatchingLogic_witnessed_alphaFreshWitnessed_of_isMCS_counterexample
-- name    : MatchingLogic.witnessed_alphaFreshWitnessed_of_isMCS_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:13.782463+00:00
-- url     : https://prove2.me/theorems/db5bd4ca-2e2f-4b13-b20d-cba04e2f8f44
-- title:
--   Matching Logic: witnessed alpha Fresh Witnessed of is MCS counterexample
-- statement:
--   Concrete MCS counterexample to the alpha-relaxed collapse.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L492-L497
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L492-L497

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section

theorem MatchingLogic.witnessed_alphaFreshWitnessed_of_isMCS_counterexample :
    ∃ Gamma : Set (Pattern AlphaWitnessSig Nat),
      IsMCS Gamma ∧ Witnessed Gamma ∧ ¬ AlphaFreshWitnessed Gamma := by sorry
