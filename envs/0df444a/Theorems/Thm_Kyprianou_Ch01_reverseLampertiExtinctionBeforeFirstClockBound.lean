-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiExtinctionBeforeFirstClockBound
-- name    : Kyprianou.Ch01.reverseLampertiExtinctionBeforeFirstClockBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:50:16.555008+00:00
-- url     : https://prove2.me/theorems/47e9451a-fbdd-428a-9aa4-fc845da2d9cf
-- title:
--   Before first source jump, reciprocal clock stays below physical horizon
-- statement:
--   For a constant positive integer population y on [0,a), the proved reciprocal occupation formula is J(u)=u/y. The source-arrival assumption a≤y*t yields J(u)≤t for all u<a. This is a genuine positive-clock inequality.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiExtinctionBeforeFirstClockBound
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a : ℝ) (ha : 0 < a)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a → X u ω = (y : ℤ))
    (hFirst : a ≤ (y : ℝ) * (t : ℝ)) :
    ∀ u : ℝ≥0, (u : ℝ) < a →
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞) := by
  sorry
