-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise55ZeroPrefactor
-- name    : Kyprianou.Ch05.exercise55ZeroPrefactor
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T16:18:41.864798+00:00
-- url     : https://prove2.me/theorems/c4d0369d-c2be-4d97-af8a-2bc60a12f763
-- title:
--   Degenerate zero-prefactor discounted passage formula
-- statement:
--   Nonnegative exponent and discount force each to vanish. With beta zero, integrate the finite passage indicator; with beta positive, the Chapter 1 unit-Laplace result makes the path zero.
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

theorem Kyprianou.Ch05.exercise55ZeroPrefactor
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
    (alpha beta x : Real) (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hx : 0 < x)
    (hz : alpha + Phi beta = 0) :
    (beta = 0 → exponentialFirstPassageMoment P Y death alpha beta x =
      (P {w : Omega | PassageFinite Y death x w}).toReal) ∧
    (0 < beta → exponentialFirstPassageMoment P Y death alpha beta x = 0) := by
  sorry
