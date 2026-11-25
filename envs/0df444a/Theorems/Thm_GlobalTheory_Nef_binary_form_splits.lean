-- Prove2me | Theorems.Thm_GlobalTheory_Nef_binary_form_splits
-- name    : GlobalTheory.Nef.binary_form_splits
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:55.777428+00:00
-- url     : https://prove2.me/theorems/67d832c3-97f5-4dd6-baf2-2c96b7b5d1e3
-- title:
--   Nef: binary form splits
-- statement:
--   The Nef construction uses the binary form splits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BinaryFormSplits.lean#L40-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BinaryFormSplits.lean#L40-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BinaryFormSplits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.binary_form_splits : ∀ (F : Type) [Field F] (m : ℕ) (p : Fin (m + 1) → F), p ≠ 0 →
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (c : E)
      (s t : Fin m → E), c ≠ 0 ∧ (∀ j, ![s j, t j] ≠ 0) ∧
      ∀ (A : Type) [CommRing A] [Algebra E A] (x y : A),
        ∑ i : Fin (m + 1), algebraMap E A (algebraMap F E (p i)) * y ^ (i : ℕ) * x ^ (m - i) =
          algebraMap E A c * ∏ j, (algebraMap E A (s j) * x + algebraMap E A (t j) * y) := by sorry
