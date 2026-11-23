-- Prove2me | Theorems.Thm_GlobalTheory_AbsFubini_core
-- name    : GlobalTheory.AbsFubini.core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:42.609926+00:00
-- url     : https://prove2.me/theorems/865306a4-ca2e-4de6-b293-5400aab25e7a
-- title:
--   Abs Fubini: core
-- statement:
--   The Abs Fubini construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L30-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L30-L78

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

theorem GlobalTheory.AbsFubini.core {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞} {b₁ : X₁ → ℝ≥0∞} {b₂ : X₂ → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂))
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) {N₁ : X₁ → ℝ≥0∞} {N₂ : X₂ → ℝ≥0∞}
    (hN₁ : ∀ x, ∫⁻ y, a₁ x y ^ 2 ∂ν ≤ N₁ x ^ 2) (hN₂ : ∀ x, ∫⁻ y, a₂ x y ^ 2 ∂ν ≤ N₂ x ^ 2) :
    ∫⁻ y, (∫⁻ x₁, a₁ x₁ y * b₁ x₁ ∂μ₁) * (∫⁻ x₂, a₂ x₂ y * b₂ x₂ ∂μ₂) ∂ν ≤
      (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) := by sorry
