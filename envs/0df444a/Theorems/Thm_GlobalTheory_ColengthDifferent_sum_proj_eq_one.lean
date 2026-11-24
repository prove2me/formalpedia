-- Prove2me | Theorems.Thm_GlobalTheory_ColengthDifferent_sum_proj_eq_one
-- name    : GlobalTheory.ColengthDifferent.sum_proj_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:14:46.433797+00:00
-- url     : https://prove2.me/theorems/1a492509-206a-4f77-8bda-201d4d3d4ff6
-- title:
--   Colength Different: sum proj eq one
-- statement:
--   The Colength Different construction uses the sum proj eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L108-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L108-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.ColengthDifferent.sum_proj_eq_one {F : Type} [Field F] [CharZero F] {ι : Type} [Fintype ι]
    (σ : ι → (E →+* F)) (hσ : Function.Injective σ) (hcard : Fintype.card ι = Module.finrank ℚ E)
    {R : Type} [Ring R] [Algebra F R] (A : 𝓞 E →+* R)
    (δ : ι → 𝓞 E) (hδ0 : ∀ i, δ i ≠ 0) (c : ι → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E)
    (hc : ∀ i k, algebraMap (𝓞 E) E (c i k) =
      algebraMap (𝓞 E) E (δ i) * (integralBasis E).traceDual k) :
    ∑ i, (σ i (algebraMap (𝓞 E) E (δ i)))⁻¹ •
      ∑ k, σ i (algebraMap (𝓞 E) E (c i k)) • A (RingOfIntegers.basis E k) = 1 := by sorry
