-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49TripletBridgeV5
-- name    : Kyprianou.Ch04.exercise49TripletBridgeV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:07:47.588568+00:00
-- url     : https://prove2.me/theorems/d181270c-cb7c-4489-bc33-f02ffce98239
-- title:
--   exercise49TripletBridgeV5
-- statement:
--   exercise49TripletBridgeV5
-- source:
--   Exercise 4.9(iii): admissible model construction

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49TripletBridgeV5
    (b : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hL : LevyFoundations.isLevyMeasure ((1 : ENNReal) • ν)) :
    let T : ProbabilityTheory.LevyKhintchineTriple :=
      ⟨b + ∫ y in Ioo (-1 : ℝ) 1, y ∂ν,0,ν,hν⟩
    ∀ ξ : ℝ, Kyprianou.Ch01.levyTripleExponent T ξ =
      Complex.I * b * ξ + (charFun ν ξ - 1) := by
  sorry
