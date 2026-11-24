-- Prove2me | Theorems.Thm_GlobalTheory_classNumber_le_of_finrank_eq_two_mul
-- name    : GlobalTheory.classNumber_le_of_finrank_eq_two_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:35.343982+00:00
-- url     : https://prove2.me/theorems/2f7a22fe-4250-4ab3-878e-75a90fec587e
-- title:
--   Global Theory: class Number le of finrank eq two mul
-- statement:
--   The Global Theory construction uses the class Number le of finrank eq two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L294-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L294-L297

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]

theorem GlobalTheory.classNumber_le_of_finrank_eq_two_mul {f : ℕ} (hf : finrank ℚ K = 2 * f) :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ (2 * f) := by sorry
