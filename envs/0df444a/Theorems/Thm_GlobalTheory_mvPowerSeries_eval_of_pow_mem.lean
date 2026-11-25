-- Prove2me | Theorems.Thm_GlobalTheory_mvPowerSeries_eval_of_pow_mem
-- name    : GlobalTheory.mvPowerSeries_eval_of_pow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:14.451842+00:00
-- url     : https://prove2.me/theorems/ab775ece-85f5-46e5-8713-4a87684963e6
-- title:
--   Global Theory: mv Power Series eval of pow mem
-- statement:
--   The Global Theory construction uses the mv Power Series eval of pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L55-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L55-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open NilpotentEval

theorem GlobalTheory.mvPowerSeries_eval_of_pow_mem : ∀ (A : Type) [CommRing A] (K : Ideal A) (σ : Type) [Finite σ] (a : σ → A), (∀ j, ∃ M : ℕ, a j ^ M ∈ K) → (IsAdicComplete K A → ∀ (R : Type) [CommRing R] [Algebra R A], ∃ ψ : MvPowerSeries σ R →ₐ[R] A, ∀ j, ψ (MvPowerSeries.X j) = a j) ∧ (IsHausdorff K A → ∀ (T : Type) [CommRing T] (ψ ψ' : MvPowerSeries σ T →+* A), (∀ t, ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)) → (∀ j, ψ (MvPowerSeries.X j) = a j) → (∀ j, ψ' (MvPowerSeries.X j) = a j) → ψ = ψ') := by sorry
