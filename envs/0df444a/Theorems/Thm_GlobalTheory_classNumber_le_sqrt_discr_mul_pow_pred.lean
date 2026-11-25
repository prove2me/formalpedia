-- Prove2me | Theorems.Thm_GlobalTheory_classNumber_le_sqrt_discr_mul_pow_pred
-- name    : GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:53.952835+00:00
-- url     : https://prove2.me/theorems/a4be554d-4e98-432d-9075-91e3b42b8b73
-- title:
--   Global Theory: class Number le sqrt discr mul pow pred
-- statement:
--   The Global Theory construction uses the class Number le sqrt discr mul pow pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L263-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L263-L284

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

theorem GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ (finrank ℚ K - 1) := by sorry
