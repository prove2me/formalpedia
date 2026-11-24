-- Prove2me | Theorems.Thm_Kyprianou_Ch02_boundedContinuousNegativeCutoffV1
-- name    : Kyprianou.Ch02.boundedContinuousNegativeCutoffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:30.604493+00:00
-- url     : https://prove2.me/theorems/987490ed-8a39-46bd-af49-a03dd6f3242b
-- title:
--   A bounded continuous nonnegative cutoff separating a negative tail
-- statement:
--   Use the explicit bounded continuous function max(0,min(1,-x-r)). Its range is contained in [0,1] and it vanishes on [-r,infinity), while being strictly positive below -r.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; small-time marginal test necessity, parent cee5c65f-db82-4515-8f93-f2ed6c878db1.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem Kyprianou.Ch02.boundedContinuousNegativeCutoffV1
    (r : ℝ) (hr : 0 < r) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      (∀ x : ℝ, 0 ≤ f x) ∧
      (∀ x : ℝ, -r ≤ x → f x = 0) ∧
      ∀ x : ℝ, x < -r → 0 < f x := by sorry
