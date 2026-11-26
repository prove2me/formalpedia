-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedOvershootUnconditionalTransformV1
-- name    : Kyprianou.Ch05.killedOvershootUnconditionalTransformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T22:04:43.35119+00:00
-- url     : https://prove2.me/theorems/ff3b5741-3e3d-40c3-9afd-bc174a0ba6db
-- title:
--   Unconditional Laplace transform of the killed overshoot
-- statement:
--   The exponential overshoot payoff on finite killed passage is the potential tail Laplace integral multiplied by the killed Laplace exponent. Use the strict-clock decomposition of weighted occupation, independence of exponential killing, and the strong Markov property at the passage clock.
-- source:
--   Kyprianou (2006), Chapter 5, Exercise 5.8.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology

theorem Kyprianou.Ch05.killedOvershootUnconditionalTransformV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real)
    (Phi : Real → Real) (U : Real → Measure Real)
    (hEta : 0 < eta)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
         Real.exp (-(t : Real) * (Phi theta-eta)))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (beta x : ℝ) (hbeta : 0 ≤ beta) (hx : 0 ≤ x) :
    (∫ w in {w : Omega | PassageFinite Y death x w},
       Real.exp (-beta*passageOvershoot Y death x w) ∂P) =
      Phi beta * (∫ z in Ioi x, Real.exp (-beta*(z-x)) ∂(U 0)) := by
  sorry
