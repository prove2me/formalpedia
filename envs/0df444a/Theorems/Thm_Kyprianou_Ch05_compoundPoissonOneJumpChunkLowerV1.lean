-- Prove2me | Theorems.Thm_Kyprianou_Ch05_compoundPoissonOneJumpChunkLowerV1
-- name    : Kyprianou.Ch05.compoundPoissonOneJumpChunkLowerV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T13:02:45.287796+00:00
-- url     : https://prove2.me/theorems/5d4e6407-0e9f-5da4-82c7-654afad9ab72
-- title:
--   Compound Poisson one-jump chunk lower bound from the driver count law
-- statement:
--   The count-one event has Poisson probability rt exp(-rt); it is independent of the first mark, and the compound path on that event is drift plus the first mark. Choose a small time horizon with survival factor at least three quarters.
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

theorem Kyprianou.Ch05.compoundPoissonOneJumpChunkLowerV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (r : NNReal) (hr : 0 < r) (F : Measure ℝ) [IsProbabilityMeasure F]
    (tau M : ℕ → Omega → ℝ)
    (hDriver : LevyFoundations.IsCompoundPoissonDriver tau M r F P)
    (hCount : ∀ t : NNReal,
      P.map (fun w => LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival tau n w) (t : ℝ)) = poissonMeasure (r*t))
    (d a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Ioc (0 : ℝ) delta,
      ENNReal.ofReal (3*t/4) * ((r : ENNReal) • F) (Icc a b) ≤
        P {w | LevyFoundations.compoundPoisson d tau M t w ∈
          {z : ℝ | ∃ y ∈ Icc a b, z = d*t+y}} := by
  sorry
