-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_iteratedDeriv_integral
-- name    : GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:05.898807+00:00
-- url     : https://prove2.me/theorems/3104f6d5-444b-495e-9d8d-76da366a3c2a
-- title:
--   Hol Mean: iterated Deriv integral
-- statement:
--   The Hol Mean construction uses the iterated Deriv integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L210-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L210-L240

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
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {U : Set ℂ}

theorem GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral (hU : IsOpen U) (r : ℕ) : ∀ G : ℂ → Ω → ℂ,
    (∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) →
    (∀ z ∈ U, AEStronglyMeasurable (G z) μ) →
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ z ∈ V ∩ U, ∀ ω, ‖G z ω‖ ≤ g ω) →
    ∀ z ∈ U, iteratedDeriv r (fun w => ∫ ω, G w ω ∂μ) z =
      ∫ ω, iteratedDeriv r (fun w => G w ω) z ∂μ := by sorry
