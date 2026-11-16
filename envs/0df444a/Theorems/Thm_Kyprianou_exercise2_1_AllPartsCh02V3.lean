-- Prove2me | Theorems.Thm_Kyprianou_exercise2_1_AllPartsCh02V3
-- name    : Kyprianou.exercise2_1_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:22:48.5009+00:00
-- url     : https://prove2.me/theorems/2004a3aa-1f5c-4edd-8bf7-f67523bab94c
-- title:
--   Exercise 2.1: countable sums of independent Poisson laws
-- statement:
--   Both parts: a countable sum of independent Poisson variables has the Poisson law with rate the sum of finite rates, almost surely finite, and equals infinity almost surely when the total rate is infinite. Use the natural ENNReal count for the infinite case.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.1, pp. 62-66; author solutions pp. 307-311; corrections recorded where needed

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem exercise2_1_AllPartsCh02V3
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hlaw : ∀ k, P.map (N k) = ProbabilityTheory.poissonMeasure (rate k))
    (hind : ProbabilityTheory.iIndepFun N P) :
    (((∑' k, (rate k : ℝ≥0∞)) < ⊤) →
       (P.map (fun ω => ∑' k, ((N k ω : ℕ) : ℝ≥0∞)) =
          (ProbabilityTheory.poissonMeasure
            ((∑' k, (rate k : ℝ≥0∞)).toNNReal)).map
              (Nat.cast : ℕ → ENNReal)) ∧
       (∀ᵐ ω ∂P, (∑' k, ((N k ω : ℕ) : ℝ≥0∞)) < ⊤)) ∧
    (((∑' k, (rate k : ℝ≥0∞)) = ⊤) →
       ∀ᵐ ω ∂P, (∑' k, ((N k ω : ℕ) : ℝ≥0∞)) = ⊤)
      := by sorry

end Kyprianou
