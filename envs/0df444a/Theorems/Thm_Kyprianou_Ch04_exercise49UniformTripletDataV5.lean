-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49UniformTripletDataV5
-- name    : Kyprianou.Ch04.exercise49UniformTripletDataV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:09:49.41617+00:00
-- url     : https://prove2.me/theorems/a898e869-4329-4ac4-b547-0a7787280381
-- title:
--   exercise49UniformTripletDataV5
-- statement:
--   exercise49UniformTripletDataV5
-- source:
--   Exercise 4.9(iii): unconditional counterexample

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49UniformTripletDataV5
    (b : ℝ) :
    ∃ T : ProbabilityTheory.LevyKhintchineTriple,
      (T.gaussianVariance = 0 ∧
        (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂T.levyMeasure) < ⊤) ∧
      b = T.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂T.levyMeasure ∧
      ∀ ξ : ℝ, Kyprianou.Ch01.levyTripleExponent T ξ =
        Complex.I * b * ξ + (charFun ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ξ - 1) := by
  sorry
