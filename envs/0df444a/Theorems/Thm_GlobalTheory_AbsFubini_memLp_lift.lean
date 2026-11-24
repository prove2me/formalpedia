-- Prove2me | Theorems.Thm_GlobalTheory_AbsFubini_memLp_lift
-- name    : GlobalTheory.AbsFubini.memLp_lift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:11.914276+00:00
-- url     : https://prove2.me/theorems/41e94a0f-f0cd-42bc-af24-c33a3bf1c4cf
-- title:
--   Abs Fubini: mem Lp lift
-- statement:
--   The Abs Fubini construction uses the mem Lp lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L80-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L80-L99

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

theorem GlobalTheory.AbsFubini.memLp_lift {k : X₁ → Y → ℂ} {u : X₁ → ℂ} (hk : Measurable (Function.uncurry k))
    (hu : Measurable u) {N : X₁ → ℝ≥0∞} (hN : ∀ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂ν ≤ N x ^ 2)
    (hfin : ∫⁻ x, N x * ‖u x‖ₑ ∂μ₁ ≠ ⊤) :
    MemLp (fun y => ∫ x, k x y * u x ∂μ₁) 2 ν := by sorry
