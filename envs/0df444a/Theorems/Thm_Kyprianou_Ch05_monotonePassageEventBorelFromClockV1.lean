-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotonePassageEventBorelFromClockV1
-- name    : Kyprianou.Ch05.monotonePassageEventBorelFromClockV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:19:39.887073+00:00
-- url     : https://prove2.me/theorems/75101a78-5543-55ba-a9e1-bbf71bc6270d
-- title:
--   Borel marked crossing event from a measurable strict crossing clock
-- statement:
--   Construct Borel boundary values using countable rational evaluations approaching the finite clock from each side. A monotone path has at most one positive-overshoot crossing. Its killed crossing coincides with its unkilled crossing exactly when it precedes death; genuine left limits agree on the common conull set. Establish the deterministic sum equality and the event equality separately.
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

theorem Kyprianou.Ch05.monotonePassageEventBorelFromClockV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x)
    (T : (NNReal → ℝ) → ENNReal) (hTm : Measurable T)
    (hT : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t})) :
    ∃ C : Set (NNReal → ℝ), MeasurableSet C ∧
      ({w | PassageFinite Y death x w ∧ 0 < passageOvershoot Y death x w ∧
          passageOvershoot Y death x w ∈ A ∧ passageUndershoot Y Yleft death x w ∈ B}
        =ᵐ[P] {w | (fun t => Y t w) ∈ C ∧ T (fun t => Y t w) < death w}) ∧
      ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        (∀ t, 0 < t → ∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) →
        (if f ∈ C ∧ T f ≠ ⊤ then ENNReal.ofReal (Real.exp (-eta*(T f).toReal)) else 0) =
          ∑' t : NNReal, if 0 < t ∧ f t > x ∧
            Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
            f t - x ∈ A ∧ x - Function.leftLim f t ∈ B then
            ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0 := by
  sorry
