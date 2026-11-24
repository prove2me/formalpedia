-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_series_step
-- name    : GlobalTheory.CompanionTheory.HolMean.series_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:17.60282+00:00
-- url     : https://prove2.me/theorems/ffb5ca6a-fbd1-402f-a18c-26612ff41c9d
-- title:
--   Hol Mean: series step
-- statement:
--   The Hol Mean construction uses the series step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L33-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L33-L59

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean
variable {κ : Type} {U : Set ℂ}

theorem GlobalTheory.CompanionTheory.HolMean.series_step (hU : IsOpen U) (F : κ → ℂ → ℂ) (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖F k z‖ ≤ u k) :
    DifferentiableOn ℂ (fun w => ∑' k, F k w) U ∧
    (∀ z ∈ U, deriv (fun w => ∑' k, F k w) z = ∑' k, deriv (F k) z) ∧
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖deriv (F k) z‖ ≤ u k) := by sorry
