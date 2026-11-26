-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneMarkedCrossingSumV1
-- name    : Kyprianou.Ch05.monotoneMarkedCrossingSumV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:14:57.757796+00:00
-- url     : https://prove2.me/theorems/e62dea8c-ec39-45bf-9baf-5feca53893c8
-- title:
--   Discounted sum at the unique monotone marked crossing
-- statement:
--   The proved uniqueness lemma places every nonzero summand at the finite first-passage clock. Collapse the sum to that singleton, including the infinite-clock case.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.monotoneMarkedCrossingSumV1
    (f : NNReal → ℝ) (hm : Monotone f) (x eta : ℝ) (A B : Set ℝ)
    (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t})) :
    (if 0 < T.toNNReal ∧ f T.toNNReal > x ∧
        Function.leftLim f T.toNNReal ∈ Icc (0 : ℝ) x ∧
        f T.toNNReal - x ∈ A ∧ x - Function.leftLim f T.toNNReal ∈ B ∧ T ≠ ⊤
      then ENNReal.ofReal (Real.exp (-eta*T.toReal)) else 0) =
      ∑' t : NNReal, if 0 < t ∧ f t > x ∧
        Function.leftLim f t ∈ Icc (0 : ℝ) x ∧ f t - x ∈ A ∧
        x - Function.leftLim f t ∈ B then ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0 := by
  sorry
