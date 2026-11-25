-- Prove2me | Theorems.Thm_GlobalTheory_classNumber_le_abs_discr_of_finrank_eq_two
-- name    : GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:34.018802+00:00
-- url     : https://prove2.me/theorems/c6569426-90de-4004-a5cb-dd39ebd1e4dd
-- title:
--   Global Theory: class Number le abs discr of finrank eq two
-- statement:
--   The Global Theory construction uses the class Number le abs discr of finrank eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ClassNumberLeAbsDiscrOfFinrankEqTwo.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ClassNumberLeAbsDiscrOfFinrankEqTwo.lean#L10-L23

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

theorem GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two (K : Type) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) :
    (NumberField.classNumber K : ℝ) ≤ |(NumberField.discr K : ℝ)| := by sorry
