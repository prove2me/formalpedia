-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise55FutureFactorOfCompleteMarkovLaw
-- name    : Kyprianou.Ch05.exercise55FutureFactorOfCompleteMarkovLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:46:12.546518+00:00
-- url     : https://prove2.me/theorems/f148f9c2-87e4-42d8-a39f-945b380c1151
-- title:
--   Unkilled subordinator discounted future factor via complete-space strong Markov
-- statement:
--   Transfer the stopped future law to the completed original probability space, derive the joint stopped-time/state and increment factor, and transfer the resulting expectation back. Zero killing makes the strict upcrossing equal to the ordinary strict hitting clock.
-- source:
--   Kyprianou (2006), Exercise 5.5(i); Chapter 3 strong Markov and entrance times.

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

theorem Kyprianou.Ch05.exercise55FutureFactorOfCompleteMarkovLaw
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
    (hMarkov : CompleteStrictPassageMarkovLaw) :
    ∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
      ∀ s : NNReal,
        (∫ w : Omega,
          if PassageFinite Y death x w then
            Real.exp (-alpha * ((passageFiniteTime Y death x w + s : NNReal) : Real)
              - beta * Y (passageFiniteTime Y death x w + s) w)
          else 0 ∂P) =
        Real.exp (-(s : Real) * (alpha + Phi beta)) *
          exponentialFirstPassageMoment P Y death alpha beta x := by
  sorry
