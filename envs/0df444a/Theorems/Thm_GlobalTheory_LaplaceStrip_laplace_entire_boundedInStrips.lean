-- Prove2me | Theorems.Thm_GlobalTheory_LaplaceStrip_laplace_entire_boundedInStrips
-- name    : GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:42.071066+00:00
-- url     : https://prove2.me/theorems/8cb8a88a-003e-4e7e-a1f3-0cab061bafd2
-- title:
--   Laplace Strip: laplace entire bounded In Strips
-- statement:
--   The Laplace Strip construction uses the laplace entire bounded In Strips property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaplaceIntegralEntireBoundedInVerticalStrips.lean#L17-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaplaceIntegralEntireBoundedInVerticalStrips.lean#L17-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplaceIntegralEntireBoundedInVerticalStrips
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.LaplaceStrip

theorem GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ)
    (hℓ : Measurable ℓ) (hg : MeasureTheory.AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    (hint : ∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by sorry
