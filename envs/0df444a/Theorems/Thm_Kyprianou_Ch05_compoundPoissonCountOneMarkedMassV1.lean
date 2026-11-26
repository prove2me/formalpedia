-- Prove2me | Theorems.Thm_Kyprianou_Ch05_compoundPoissonCountOneMarkedMassV1
-- name    : Kyprianou.Ch05.compoundPoissonCountOneMarkedMassV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T13:07:58.492553+00:00
-- url     : https://prove2.me/theorems/79f0bfce-8a98-53b5-9982-5d37ea6ceb9f
-- title:
--   Probability of the one-jump event with its first mark in a measurable set
-- statement:
--   The one-jump event depends only on two interarrivals. The joint driver independence gives independence from the first mark. Apply the existing Poisson count law.
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

theorem Kyprianou.Ch05.compoundPoissonCountOneMarkedMassV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (r : NNReal) (hr : 0 < r) (F : Measure ℝ) [IsProbabilityMeasure F]
    (tau M : ℕ → Omega → ℝ)
    (hDriver : LevyFoundations.IsCompoundPoissonDriver tau M r F P)
    (hCount : ∀ t : NNReal,
      P.map (fun w => LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival tau n w) (t : ℝ)) = poissonMeasure (r*t))    (t : ℝ) (ht : 0 ≤ t) (B : Set ℝ) (hB : MeasurableSet B) :
    P {w | LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival tau n w) t = 1 ∧ M 0 w ∈ B} =
      ENNReal.ofReal (Real.exp (-(r:ℝ)*t) * ((r:ℝ)*t)) * F B := by
  sorry
