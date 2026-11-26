-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPassageDiscountedPathFunctionalV1
-- name    : Kyprianou.Ch05.killedPassageDiscountedPathFunctionalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:53:30.389632+00:00
-- url     : https://prove2.me/theorems/88681046-136d-57d0-95e5-2d2a4846b280
-- title:
--   Discounted measurable path functional for positive killed first passage
-- statement:
--   Recover the crossing time, right and left values through countable dense coordinate evaluations. Independent exponential death gives the discounted path functional; uniqueness of the strictly crossing jump identifies its value with the weighted sum.
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

theorem Kyprianou.Ch05.killedPassageDiscountedPathFunctionalV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x) :
    ∃ H : (NNReal → ℝ) → ENNReal, Measurable H ∧
      positiveJointPassageLaw P Y Yleft death x A B =
        ∫⁻ f, H f ∂(P.map (fun w t => Y t w)) ∧
      ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        (∀ t, 0 < t → ∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) →
        H f = ∑' t : NNReal, if 0 < t ∧ f t > x ∧
          Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
          f t - x ∈ A ∧ x - Function.leftLim f t ∈ B then
          ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0 := by
  sorry
