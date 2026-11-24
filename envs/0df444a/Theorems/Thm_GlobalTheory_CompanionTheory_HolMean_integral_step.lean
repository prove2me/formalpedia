-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_integral_step
-- name    : GlobalTheory.CompanionTheory.HolMean.integral_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:03.486543+00:00
-- url     : https://prove2.me/theorems/e5725b6c-754e-4e25-a74e-c0f8de109322
-- title:
--   Hol Mean: integral step
-- statement:
--   The Hol Mean construction uses the integral step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L178-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L178-L208

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

theorem GlobalTheory.CompanionTheory.HolMean.integral_step (hU : IsOpen U) (G : ℂ → Ω → ℂ)
    (hd : ∀ ω, DifferentiableOn ℂ (fun z => G z ω) U)
    (hm : ∀ z ∈ U, AEStronglyMeasurable (G z) μ)
    (hb : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ z ∈ V ∩ U, ∀ ω, ‖G z ω‖ ≤ g ω) :
    (∀ z ∈ U, HasDerivAt (fun w => ∫ ω, G w ω ∂μ) (∫ ω, deriv (fun w => G w ω) z ∂μ) z) ∧
    (∀ z ∈ U, AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ) ∧
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ z ∈ V ∩ U, ∀ ω, ‖deriv (fun w => G w ω) z‖ ≤ g ω) := by sorry
