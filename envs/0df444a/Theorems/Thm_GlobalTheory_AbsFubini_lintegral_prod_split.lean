-- Prove2me | Theorems.Thm_GlobalTheory_AbsFubini_lintegral_prod_split
-- name    : GlobalTheory.AbsFubini.lintegral_prod_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:47.531797+00:00
-- url     : https://prove2.me/theorems/204c4d5e-e29c-4f58-8ca6-adf3c128a303
-- title:
--   Abs Fubini: lintegral prod split
-- statement:
--   The Abs Fubini construction uses the lintegral prod split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L22-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralKernelLiftsFubiniSigmaFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ENNReal
open GlobalTheory GlobalTheory.AbsFubini
variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]

theorem GlobalTheory.AbsFubini.lintegral_prod_split {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂)) (y : Y) :
    (∫⁻ x₁, a₁ x₁ y ∂μ₁) * (∫⁻ x₂, a₂ x₂ y ∂μ₂) = ∫⁻ p : X₁ × X₂, a₁ p.1 y * a₂ p.2 y ∂μ₁.prod μ₂ := by sorry
