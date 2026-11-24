-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_local
-- name    : GlobalTheory.CompanionTheory.EisTube.tubeShift_local
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:21.009802+00:00
-- url     : https://prove2.me/theorems/4acad8c7-c233-4613-905e-c075066efe65
-- title:
--   Eis Tube: tube Shift local
-- statement:
--   The Eis Tube construction uses the tube Shift local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L114-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L114-L217

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.tubeShift_local {ι : Type} [Fintype ι] (Ω : Set (ι → ℝ)) (H : (ι → ℂ) → ℂ)
    (hH : DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω})
    (x₀ x₁ : ι → ℝ) (R C : ℝ) (hK : Metric.closedBall x₀ R ⊆ Ω)
    (hC : ∀ x ∈ Metric.closedBall x₀ R, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2))
    (hx : dist x₁ x₀ ≤ R / 2) :
    (∫ y : ι → ℝ, H (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I)) =
      ∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I) := by sorry
