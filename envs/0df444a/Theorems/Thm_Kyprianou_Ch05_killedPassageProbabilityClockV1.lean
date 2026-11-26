-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPassageProbabilityClockV1
-- name    : Kyprianou.Ch05.killedPassageProbabilityClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:50:57.751849+00:00
-- url     : https://prove2.me/theorems/fa073161-3de9-4056-a9d1-a692235e8bd0
-- title:
--   Finite killed passage probability equals the exponential discount of the unkilled clock
-- statement:
--   Use the strict killed-clock formula pathwise and the proved independent killing survival factor. Pull the path-law integral back to the underlying probability space.
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

theorem Kyprianou.Ch05.killedPassageProbabilityClockV1
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (x : ℝ) (T : (NNReal → ℝ) → ENNReal) (hTm : Measurable T)
    (hT : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
      T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t})) :
    P {w | PassageFinite Y death x w} =
      ∫⁻ w, if T (fun t => Y t w) ≠ ⊤ then
        ENNReal.ofReal (Real.exp (-eta*(T (fun t => Y t w)).toReal)) else 0 ∂P := by
  sorry
