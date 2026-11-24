-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_cauchy_nhds
-- name    : GlobalTheory.CompanionTheory.HolMean.cauchy_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:09.605629+00:00
-- url     : https://prove2.me/theorems/dbf7493f-7346-41f0-98cf-54b2467b3f37
-- title:
--   Hol Mean: cauchy nhds
-- statement:
--   The Hol Mean construction uses the cauchy nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L7-L27

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

theorem GlobalTheory.CompanionTheory.HolMean.cauchy_nhds {U V : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hV : V ∈ 𝓝 z₀) :
    ∃ R : ℝ, 0 < R ∧ ∃ W ∈ 𝓝 z₀, W ⊆ U ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∀ C : ℝ, (∀ z ∈ V ∩ U, ‖f z‖ ≤ C) → ∀ z ∈ W, ‖deriv f z‖ ≤ C / R := by sorry
