-- Prove2me | Theorems.Thm_Kyprianou_Ch02_variationOfMonotoneApproximantsTendstoV1
-- name    : Kyprianou.Ch02.variationOfMonotoneApproximantsTendstoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:33:32.373863+00:00
-- url     : https://prove2.me/theorems/218008b6-e613-4b3a-84b1-14c5da9c4cbd
-- title:
--   Variation converges under monotone pointwise approximants
-- statement:
--   Use Mathlib eVariationOn.lowerSemicontinuous_aux for the lower bound and monotone composition with the image subset for the upper bound.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.variationOfMonotoneApproximantsTendstoV1
    (f : ℝ≥0 → ℝ) (s : Set ℝ≥0)
    (r : ℕ → ℝ≥0 → ℝ≥0)
    (hm : ∀ n, MonotoneOn (r n) s)
    (hmem : ∀ n, MapsTo (r n) s s)
    (hlim : ∀ x ∈ s, Tendsto (fun n => f (r n x)) atTop (nhds (f x))) :
    Tendsto (fun n => eVariationOn f (r n '' s)) atTop
      (nhds (eVariationOn f s)) := by sorry
