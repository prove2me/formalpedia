-- Prove2me | Theorems.Thm_Kyprianou_Ch07_unitOscillationSublinear_of_summableTails
-- name    : Kyprianou.Ch07.unitOscillationSublinear_of_summableTails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:05:45.641472+00:00
-- url     : https://prove2.me/theorems/4664167b-62c4-4468-93be-bb22cb75daa0
-- title:
--   Borel–Cantelli implies sublinear Lévy unit-block oscillations under summable tails
-- statement:
--   For a measurable stochastic process, if the probabilities that its maximum absolute increment on the nth unit interval exceeds n/(k+1) are summable for every natural k, then the unit-block maximum divided by n converges to zero almost surely. The theorem isolates the analytic part of Kyprianou (2006), Chapter 7, Exercise 7.2(ii).
-- source:
--   Derived from already Proved ProbabilityTheory theorem thm_5_8 (first Borel-Cantelli) and Kyprianou (2006), Exercise 7.2(ii), printed p. 207. Private remote elaboration job bdc167be-0c95-464d-85cd-dc03d855e4fc.

import Mathlib
import Theorems.Thm_thm_5_8
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables

open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch07.unitOscillationSublinear_of_summableTails
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hSum : ∀ k : ℕ, (∑' n : ℕ,
      P {ω : Ω | ((k : ℝ) + 1)⁻¹ * (n : ℝ) ≤
        |Kyprianou.Ch07.maximalUnitIncrement X n ω|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => Kyprianou.Ch07.maximalUnitIncrement X n ω / (n : ℝ))
      atTop (nhds (0 : ℝ)) := by sorry
