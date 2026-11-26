-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49AdmissibleUniformModelV5
-- name    : Kyprianou.Ch04.exercise49AdmissibleUniformModelV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:09:50.445543+00:00
-- url     : https://prove2.me/theorems/6a689857-8799-5583-b227-f4dd77d74939
-- title:
--   exercise49AdmissibleUniformModelV5
-- statement:
--   exercise49AdmissibleUniformModelV5
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

theorem Kyprianou.Ch04.exercise49AdmissibleUniformModelV5
    :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) (X : NNReal → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
      (T : ProbabilityTheory.LevyKhintchineTriple) (b : ℝ),
      IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
      (∀ t : NNReal, ∀ ξ : ℝ, charFun (P.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ)) ∧
      (T.gaussianVariance = 0 ∧
        (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂T.levyMeasure) < ⊤) ∧
      b = T.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂T.levyMeasure ∧
      0 < b ∧ ¬ (∀ᵐ w ∂P, Monotone (fun t : NNReal => X t w)) ∧
      ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop := by
  sorry
