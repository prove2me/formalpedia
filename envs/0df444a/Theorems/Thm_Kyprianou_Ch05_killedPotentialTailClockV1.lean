-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotentialTailClockV1
-- name    : Kyprianou.Ch05.killedPotentialTailClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:50:57.033668+00:00
-- url     : https://prove2.me/theorems/043346e6-31bd-4511-84de-71c96d1a1868
-- title:
--   Killed potential tail equals expected discounted strict passage occupation
-- statement:
--   Apply the exact killed occupation formula to the tail indicator and factor survival. Use the Chapter 4 jointly measurable version to justify Tonelli. The pathwise discounted tail formula then identifies the time integral.
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

theorem Kyprianou.Ch05.killedPotentialTailClockV1
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (d : ℝ) (Pi : Measure ℝ) (Phi : ℝ → ℝ)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ t : NNReal, ∀ theta : ℝ, 0 ≤ theta →
      (∫ w, Real.exp (-theta*Y t w) ∂P) = Real.exp (-(t : ℝ)*(Phi theta-eta)))
    (U : ℝ → Measure ℝ) (hPotential : IsKilledPotentialFamily P Y death U)
    (heta : 0 < eta)
    (x : ℝ) (T : (NNReal → ℝ) → ENNReal) (hTm : Measurable T)
    (hT : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
      T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}))
    (hx : 0 ≤ x) :
    U 0 (Ioi x) = ∫⁻ w, if T (fun t => Y t w) ≠ ⊤ then
      ENNReal.ofReal (Real.exp (-eta*(T (fun t => Y t w)).toReal)/eta) else 0 ∂P := by
  sorry
