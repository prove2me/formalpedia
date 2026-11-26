-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise55DiscountedPassageOfFutureFactor
-- name    : Kyprianou.Ch05.exercise55DiscountedPassageOfFutureFactor
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:46:06.300346+00:00
-- url     : https://prove2.me/theorems/ba1f08d1-54da-5dc8-ad7a-f44234fb0f9d
-- title:
--   Discounted passage identity from the future factor and occupation calculus
-- statement:
--   Use monotone paths, the potential occupation formula, Tonelli and the exponential integral to deduce the positive prefactor equality from the future factor. Treat the zero prefactor branches separately.
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

theorem Kyprianou.Ch05.exercise55DiscountedPassageOfFutureFactor
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
    (hFactor : ∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
      ∀ s : NNReal,
        (∫ w : Omega,
          if PassageFinite Y death x w then
            Real.exp (-alpha * ((passageFiniteTime Y death x w + s : NNReal) : Real)
              - beta * Y (passageFiniteTime Y death x w + s) w)
          else 0 ∂P) =
        Real.exp (-(s : Real) * (alpha + Phi beta)) *
          exponentialFirstPassageMoment P Y death alpha beta x) :
  (∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
      ((0 < alpha + Phi beta →
        IntegrableOn (fun z : Real => Real.exp (-beta*z))
          (Set.Ioi x) (U alpha) ∧
        exponentialFirstPassageMoment P Y death alpha beta x =
          (alpha + Phi beta) *
            ∫ z in Set.Ioi x, Real.exp (-beta*z) ∂(U alpha)) ∧
       (alpha + Phi beta = 0 →
         (beta = 0 →
            exponentialFirstPassageMoment P Y death alpha beta x =
              (P {omega : Omega | PassageFinite Y death x omega}).toReal) ∧
         (0 < beta →
            exponentialFirstPassageMoment P Y death alpha beta x = 0))))
 := by
  sorry
