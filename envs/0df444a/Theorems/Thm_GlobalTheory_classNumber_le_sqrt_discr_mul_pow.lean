-- Prove2me | Theorems.Thm_GlobalTheory_classNumber_le_sqrt_discr_mul_pow
-- name    : GlobalTheory.classNumber_le_sqrt_discr_mul_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:53.350583+00:00
-- url     : https://prove2.me/theorems/7b9993d1-9ad0-4d87-aa3e-27ba8058c95f
-- title:
--   Global Theory: class Number le sqrt discr mul pow
-- statement:
--   The Global Theory construction uses the class Number le sqrt discr mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L286-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L286-L292

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

theorem GlobalTheory.classNumber_le_sqrt_discr_mul_pow :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ finrank ℚ K := by sorry
