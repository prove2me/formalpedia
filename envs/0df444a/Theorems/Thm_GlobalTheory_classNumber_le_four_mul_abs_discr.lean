-- Prove2me | Theorems.Thm_GlobalTheory_classNumber_le_four_mul_abs_discr
-- name    : GlobalTheory.classNumber_le_four_mul_abs_discr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:12.311909+00:00
-- url     : https://prove2.me/theorems/831c229c-bcc3-4a7e-87c6-92f9b755f55f
-- title:
--   Global Theory: class Number le four mul abs discr
-- statement:
--   The Global Theory construction uses the class Number le four mul abs discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ClassNumberLeAbsDiscrOfFinrankEqTwo.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ClassNumberLeAbsDiscrOfFinrankEqTwo.lean#L27-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ClassNumberLeAbsDiscrOfFinrankEqTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

theorem GlobalTheory.classNumber_le_four_mul_abs_discr :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (NumberField.classNumber K : ℝ) ≤ 4 * |(NumberField.discr K : ℝ)| := by sorry
