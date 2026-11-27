-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CutoffStateRegularV5
-- name    : Kyprianou.Ch04.exercise45CutoffStateRegularV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:15:36.716457+00:00
-- url     : https://prove2.me/theorems/920dd63b-27d7-4910-9ce3-7d3ac1af13b0
-- title:
--   Physical cutoff coordinates are measurable and paths right-continuous
-- statement:
--   Physical cutoff coordinates are measurable and paths right-continuous
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii)

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory Filter Set Topology ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45CutoffStateRegularV5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L X2 Y : NNReal → Ω → ℝ)
    (b e : ℝ) (he : 0 < e)
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w)
    (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hY : ∀ t w, Y t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}, z.2 ∂(N.N w)) -
      (t : ℝ) * ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν) :
    (∀ t, AEMeasurable (Y t) P) ∧
      (∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t) := by
  sorry
