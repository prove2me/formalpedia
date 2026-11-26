-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise55OccupationShift
-- name    : Kyprianou.Ch05.exercise55OccupationShift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T16:18:31.896332+00:00
-- url     : https://prove2.me/theorems/a3572ce0-9964-5fcb-9de2-9a9a94226da9
-- title:
--   Strict passage occupation equals integrated shifted future moment
-- statement:
--   On each monotone path, occupation above the barrier starts just after the strict passage clock, with a singleton endpoint of zero time measure. Translate by this random clock, use joint a.e. measurability and Tonelli, and convert the bounded real expectation to a lintegral.
-- source:
--   Kyprianou (2006), Exercise 5.5(i); occupation shift and zero prefactor.

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Definitions.Def_Kyprianou_Ch05_CompleteStrictPassageMarkovLaw
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical

theorem Kyprianou.Ch05.exercise55OccupationShift
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (alpha beta x : Real) (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hx : 0 < x) :
    (∫⁻ z in Set.Ioi x, ENNReal.ofReal (Real.exp (-beta*z)) ∂(U alpha)) =
      ∫⁻ s in Set.Ici (0 : Real), ENNReal.ofReal
        (∫ w : Omega,
          if PassageFinite Y death x w then
            Real.exp (-alpha * ((passageFiniteTime Y death x w + Real.toNNReal s : NNReal) : Real)
              - beta * Y (passageFiniteTime Y death x w + Real.toNNReal s) w)
          else 0 ∂P) ∂volume := by
  sorry
