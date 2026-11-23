-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPiecePositiveClockCrossingWitness
-- name    : Kyprianou.Ch01.reverseLampertiTwoPiecePositiveClockCrossingWitness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:34:17.368029+00:00
-- url     : https://prove2.me/theorems/3426a8c3-0353-4400-9fc2-8f66f67d36c0
-- title:
--   Two-piece occupation clock has a crossing before the second arrival while remaining below threshold before the first
-- statement:
--   The first source stage has constant positive value y, so occupation before a is u/y≤a/y≤t. The second stage has value z=y+j-1>0. At source time c=a+z*t, which lies before b by the given second-arrival buffer, occupation equals a/y+t and therefore strictly exceeds t because a>0. Establish these two bounds using the exact ENNReal reciprocal-occupation integral and the source hypotheses. This is the only integral-specific requirement needed by the generic proved inverse-clock bracket lemma.
-- source:
--   Kyprianou (2006) §1.3.4, two-stage inverse speed occupation crossing

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiTwoPiecePositiveClockCrossingWitness
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a b : ℝ) (ha : 0 < a)
    (hAB : a < b)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a →
      X u ω = (y : ℤ))
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hPost : 0 < y + j - 1)
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    ∃ c : ℝ≥0, (c : ℝ) < b ∧
      (∀ u : ℝ≥0, (u : ℝ) < a →
        reciprocalOccupation X u ω ≤ (t : ℝ≥0∞)) ∧
      (t : ℝ≥0∞) < reciprocalOccupation X c ω := by
  sorry
