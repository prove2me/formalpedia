-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_differentiableOn_integral
-- name    : GlobalTheory.CompanionTheory.EisTube.tubeShift_differentiableOn_integral
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:18.191328+00:00
-- url     : https://prove2.me/theorems/ea7e5c77-1e41-4d87-a19c-c1c61052dd43
-- title:
--   Eis Tube: tube Shift differentiable On integral
-- statement:
--   The Eis Tube construction uses the tube Shift differentiable On integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L33-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L33-L92

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

theorem GlobalTheory.CompanionTheory.EisTube.tubeShift_differentiableOn_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → α → ℂ)
    (hol : ∀ y, DifferentiableOn ℂ (fun w => F w y) U)
    (meas : ∀ w ∈ U, AEStronglyMeasurable (F w) μ)
    (dom : ∀ w₀ ∈ U, ∀ ρ : ℝ, 0 < ρ → Metric.closedBall w₀ ρ ⊆ U →
      ∃ g : α → ℝ, Integrable g μ ∧ ∀ w ∈ Metric.closedBall w₀ ρ, ∀ y, ‖F w y‖ ≤ g y) :
    DifferentiableOn ℂ (fun w => ∫ y, F w y ∂μ) U := by sorry
