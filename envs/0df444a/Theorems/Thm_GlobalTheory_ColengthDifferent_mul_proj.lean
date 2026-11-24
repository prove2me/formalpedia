-- Prove2me | Theorems.Thm_GlobalTheory_ColengthDifferent_mul_proj
-- name    : GlobalTheory.ColengthDifferent.mul_proj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:14:38.598004+00:00
-- url     : https://prove2.me/theorems/be212a30-ecaf-445b-aa5d-261cdccd21a9
-- title:
--   Colength Different: mul proj
-- statement:
--   The Colength Different construction uses the mul proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L86-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L86-L106

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

theorem GlobalTheory.ColengthDifferent.mul_proj {T : Type} [CommRing T] (t : 𝓞 E →+* T) {R : Type} [Ring R] [Algebra T R]
    (A : 𝓞 E →+* R) {c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E} {δ : 𝓞 E}
    (hc : ∀ k, algebraMap (𝓞 E) E (c k) = algebraMap (𝓞 E) E δ * (integralBasis E).traceDual k)
    (a : 𝓞 E) :
    A a * ∑ k, t (c k) • A (RingOfIntegers.basis E k) =
      t a • ∑ k, t (c k) • A (RingOfIntegers.basis E k) := by sorry
