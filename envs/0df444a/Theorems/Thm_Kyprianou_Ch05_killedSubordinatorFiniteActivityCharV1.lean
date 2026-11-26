-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinatorFiniteActivityCharV1
-- name    : Kyprianou.Ch05.killedSubordinatorFiniteActivityCharV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:02:53.605283+00:00
-- url     : https://prove2.me/theorems/34929d6f-561d-4816-904f-82918c836c8f
-- title:
--   Finite positive Levy measure characteristic function in normalized mark form
-- statement:
--   Use the Chapter 2 nonnegative marginal and exponent analytic transforms, extend the real-axis identity, evaluate the imaginary boundary, then factor the normalized finite Levy measure.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.4.

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05 Set Complex

theorem Kyprianou.Ch05.killedSubordinatorFiniteActivityCharV1

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
    (r : NNReal) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hScale : Pi = (r : ENNReal) • F) :
    ∀ (t : NNReal) (u : ℝ),
      charFun (P.map (Y t)) u =
        Complex.exp ((t : ℝ) * (Complex.I * d * u + r * (charFun F u - 1))) := by
  sorry
