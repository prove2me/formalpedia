-- Prove2me | Theorems.Thm_GlobalTheory_AbsFubini_lintegral_mul_le_sqrt
-- name    : GlobalTheory.AbsFubini.lintegral_mul_le_sqrt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:05.684396+00:00
-- url     : https://prove2.me/theorems/b19adc4b-8bda-4dd3-bc6d-a1b126e85bdf
-- title:
--   Abs Fubini: lintegral mul le sqrt
-- statement:
--   The Abs Fubini construction uses the lintegral mul le sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L10-L15

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

theorem GlobalTheory.AbsFubini.lintegral_mul_le_sqrt (ν : Measure Y) {a₁ a₂ : Y → ℝ≥0∞} (h₁ : Measurable a₁) (h₂ : Measurable a₂) :
    ∫⁻ y, a₁ y * a₂ y ∂ν ≤
      (∫⁻ y, a₁ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) * (∫⁻ y, a₂ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) := by sorry
