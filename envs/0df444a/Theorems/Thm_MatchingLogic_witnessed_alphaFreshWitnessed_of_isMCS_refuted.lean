-- Prove2me | Theorems.Thm_MatchingLogic_witnessed_alphaFreshWitnessed_of_isMCS_refuted
-- name    : MatchingLogic.witnessed_alphaFreshWitnessed_of_isMCS_refuted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:01.328452+00:00
-- url     : https://prove2.me/theorems/f0b96f35-40de-4ca5-aaea-a937f0036d3c
-- title:
--   Matching Logic: witnessed alpha Fresh Witnessed of is MCS refuted
-- statement:
--   The proposed implication is false, even with the broad proof-theoretic
--   definition of `Pattern.AlphaEq`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L501-L506
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/AlphaFreshWitnessed.lean#L501-L506

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

theorem MatchingLogic.witnessed_alphaFreshWitnessed_of_isMCS_refuted :
    ¬ (∀ {Gamma : Set (Pattern AlphaWitnessSig Nat)},
      IsMCS Gamma → Witnessed Gamma → AlphaFreshWitnessed Gamma) := by sorry
