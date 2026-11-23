-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceInverseClockAtExtinction
-- name    : Kyprianou.Ch01.reverseLampertiTwoPieceInverseClockAtExtinction
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:26:10.694547+00:00
-- url     : https://prove2.me/theorems/f776ceae-39b8-4f8c-9f9d-b815535dfacf
-- title:
--   Inverse occupation stops exactly at the first source arrival when the population reaches zero
-- statement:
--   Under two-piece source paths with zero post-jump population, the reciprocal-speed occupation integral becomes infinite immediately after a, and no source time before a crosses physical t≥a/y. Thus the strict right inverse of the occupation clock is exactly a.
-- source:
--   Kyprianou (2006) §1.3.4, inverse reciprocal occupation at first marked jump

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiTwoPieceInverseClockAtExtinction
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a b : ℝ) (ha : 0 < a)
    (hAB : a < b)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a →
      X u ω = (y : ℤ))
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hZero : y + j - 1 = 0)
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    inverseReciprocalOccupation X t ω = (Real.toNNReal a : WithTop ℝ≥0) := by
  sorry
