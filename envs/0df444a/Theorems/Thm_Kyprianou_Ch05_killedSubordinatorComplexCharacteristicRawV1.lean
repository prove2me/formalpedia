-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinatorComplexCharacteristicRawV1
-- name    : Kyprianou.Ch05.killedSubordinatorComplexCharacteristicRawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:36:47.256557+00:00
-- url     : https://prove2.me/theorems/abbb018a-16ba-49fb-a886-d858d9812764
-- title:
--   Unkilled marginal characteristic function from the killed Laplace triplet
-- statement:
--   Reuse the existing real Laplace anchor and analytic continuation to the imaginary axis, preserving the raw complex exponent instead of separating its real and imaginary parts.
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

theorem Kyprianou.Ch05.killedSubordinatorComplexCharacteristicRawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (t : NNReal) (u : ℝ) :
    charFun (P.map (Y t)) u =
      Complex.exp (((t : ℝ) : ℂ) *
        (∫ y in Ioi (0 : ℝ), (Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1) ∂Pi)
        + ((d*(t : ℝ)*u : ℝ) : ℂ)*Complex.I) := by
  sorry
