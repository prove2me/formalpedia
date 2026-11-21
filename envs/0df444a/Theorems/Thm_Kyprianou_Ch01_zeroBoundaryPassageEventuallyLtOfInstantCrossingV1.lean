-- Prove2me | Theorems.Thm_Kyprianou_Ch01_zeroBoundaryPassageEventuallyLtOfInstantCrossingV1
-- name    : Kyprianou.Ch01.zeroBoundaryPassageEventuallyLtOfInstantCrossingV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:39:42.132577+00:00
-- url     : https://prove2.me/theorems/59ef5491-0286-43b2-a1b8-74f1c3de1199
-- title:
--   Immediate positive crossing yields eventual upper bounds for zero-level passage times
-- statement:
--   At barrier zero, immediate upward crossing yields a strict path crossing X_v>0 before every positive time horizon a. The set of levels u for which u<X_v is an open neighbourhood of zero, and the first-passage time at each such level (with zero-level reset) is bounded by v<a. Hence the passage clock is eventually below any positive real upper bound on the right-neighbourhood filter. This is the exact upper-order component of right continuity at zero.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, first-passage regularity at level zero.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.zeroBoundaryPassageEventuallyLtOfInstantCrossingV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hCross : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < X t ω)
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ u in 𝓝[Ici (0 : ℝ≥0)] 0,
      (if u = 0 then (0 : ℝ)
      else (match firstUpperPassage X (u : ℝ) ω with
      | none => (0 : ℝ)
      | some v => (v : ℝ))) < a := by
  sorry
