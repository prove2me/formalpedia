-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_holomorphic_mean
-- name    : GlobalTheory.CompanionTheory.HolMean.holomorphic_mean
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:32:15.058341+00:00
-- url     : https://prove2.me/theorems/e29caf75-5a64-4a3c-a23d-7df7d79c7df2
-- title:
--   Hol Mean: holomorphic mean
-- statement:
--   The Hol Mean construction uses the holomorphic mean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L244-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L244-L298

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

theorem GlobalTheory.CompanionTheory.HolMean.holomorphic_mean (P Ω κ : Type) [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace Ω] [Countable κ] (μ : Measure Ω) (U : Set ℂ)
    (hU : IsOpen U)
    (hball : ∀ z ∈ U, ∃ (t ρ : ℝ), 0 < ρ ∧ z ∈ Metric.ball (t : ℂ) ρ ∧ Metric.ball (t : ℂ) ρ ⊆ U)
    (F : P → ℂ → Ω → κ → ℂ) (hF : ∀ p ω k, DifferentiableOn ℂ (fun z => F p z ω k) U)
    (hFc : ∀ ω k, ContinuousOn (fun q : P × ℂ => F q.1 q.2 ω k) (Set.univ ×ˢ U))
    (hFm : ∀ p (t : ℝ), (t : ℂ) ∈ U → AEStronglyMeasurable (fun ω => ∑' k, F p t ω k) μ)
    (hB : ∀ q ∈ (Set.univ : Set P) ×ˢ U, ∃ N ∈ 𝓝 q, ∃ (M : Ω → κ → ℝ) (g : Ω → ℝ),
      (∀ ω, Summable (M ω)) ∧ Integrable g μ ∧ (∀ ω, ∑' k, M ω k ≤ g ω) ∧
      ∀ q' ∈ N, q'.2 ∈ U → ∀ ω k, ‖F q'.1 q'.2 ω k‖ ≤ M ω k) :
    ContinuousOn (fun q : P × ℂ => ∫ ω, ∑' k, F q.1 q.2 ω k ∂μ) (Set.univ ×ˢ U) ∧
      (∀ p, DifferentiableOn ℂ (fun z => ∫ ω, ∑' k, F p z ω k ∂μ) U) ∧
      ∀ p, ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ ω, ∑' k, F p z ω k ∂μ) z =
        ∫ ω, ∑' k, iteratedDeriv r (fun z => F p z ω k) z ∂μ := by sorry
