-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_binary_form_eq_mul_prod_linear
-- name    : GlobalTheory.T.exists_binary_form_eq_mul_prod_linear
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:59.002983+00:00
-- url     : https://prove2.me/theorems/b4d4e591-a478-4665-9c87-7dc0692d6a83
-- title:
--   T: exists binary form eq mul prod linear
-- statement:
--   The T construction uses the exists binary form eq mul prod linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BinaryFormSplitsStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BinaryFormSplitsStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BinaryFormSplits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BinaryFormSplitsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_binary_form_eq_mul_prod_linear : ∀ (F : Type) [Field F] (m : ℕ) (p : Fin (m + 1) → F), p ≠ 0 → ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (c : E) (s t : Fin m → E), c ≠ 0 ∧ (∀ j, ![s j, t j] ≠ 0) ∧ ∀ (A : Type) [CommRing A] [Algebra E A] (x y : A), ∑ i : Fin (m + 1), algebraMap E A (algebraMap F E (p i)) * y ^ (i : ℕ) * x ^ (m - i) = algebraMap E A c * ∏ j, (algebraMap E A (s j) * x + algebraMap E A (t j) * y) := by sorry
