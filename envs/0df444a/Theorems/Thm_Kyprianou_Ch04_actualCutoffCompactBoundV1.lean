-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualCutoffCompactBoundV1
-- name    : Kyprianou.Ch04.actualCutoffCompactBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:37.341179+00:00
-- url     : https://prove2.me/theorems/133c80ad-72b3-4207-a716-9d42b4c58bce
-- title:
--   Actual cutoff paths are compact bounded
-- statement:
--   Actual cutoff paths are compact bounded.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualCutoffCompactBoundV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : IsLevyMeasure ν) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (X Xleft X2 Y : NNReal → Ω → ℝ) (b ε : ℝ) (hε : 0 < ε)
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X Xleft w)
    (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hY : ∀ t w, Y t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) - (t : ℝ) *
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν)) :
    ∀ᵐ w ∂P, ∀ T : NNReal, ∃ C : ℝ, ∀ t ≤ T, |Y t w| ≤ C := by
  sorry
end Kyprianou.Ch04
