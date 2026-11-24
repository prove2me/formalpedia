-- Prove2me | Theorems.Thm_GlobalTheory_AbsFubini_abstract_fubini_two_lifts
-- name    : GlobalTheory.AbsFubini.abstract_fubini_two_lifts
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:11.673274+00:00
-- url     : https://prove2.me/theorems/5304d14c-fbc9-46d4-a6ce-c06c1c0a0227
-- title:
--   Abs Fubini: abstract fubini two lifts
-- statement:
--   The Abs Fubini construction uses the abstract fubini two lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L101-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L101-L153

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

theorem GlobalTheory.AbsFubini.abstract_fubini_two_lifts : ∀ {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) (ν : Measure Y) [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
    (k₁ : X₁ → Y → ℂ) (k₂ : X₂ → Y → ℂ) (u₁ : X₁ → ℂ) (u₂ : X₂ → ℂ),
    Measurable (Function.uncurry k₁) → Measurable (Function.uncurry k₂) → Measurable u₁ → Measurable u₂ →
    ∀ (N₁ : X₁ → ENNReal) (N₂ : X₂ → ENNReal),
    (∀ x, ∫⁻ y, ‖k₁ x y‖ₑ ^ 2 ∂ν ≤ N₁ x ^ 2) → (∀ x, ∫⁻ y, ‖k₂ x y‖ₑ ^ 2 ∂ν ≤ N₂ x ^ 2) →
    ∫⁻ x, N₁ x * ‖u₁ x‖ₑ ∂μ₁ ≠ ⊤ → ∫⁻ x, N₂ x * ‖u₂ x‖ₑ ∂μ₂ ≠ ⊤ →
    (∀ y, Integrable (fun x => k₁ x y * u₁ x) μ₁) → (∀ y, Integrable (fun x => k₂ x y * u₂ x) μ₂) →
    MemLp (fun y => ∫ x, k₁ x y * u₁ x ∂μ₁) 2 ν ∧ MemLp (fun y => ∫ x, k₂ x y * u₂ x ∂μ₂) 2 ν ∧
    ∫ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) ∂ν =
      ∫ p : X₁ × X₂, (∫ y, k₁ p.1 y * conj (k₂ p.2 y) ∂ν) * u₁ p.1 * conj (u₂ p.2) ∂μ₁.prod μ₂ := by sorry
