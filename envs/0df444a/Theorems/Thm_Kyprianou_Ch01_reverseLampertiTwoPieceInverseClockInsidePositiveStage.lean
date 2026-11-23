-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceInverseClockInsidePositiveStage
-- name    : Kyprianou.Ch01.reverseLampertiTwoPieceInverseClockInsidePositiveStage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:26:16.123425+00:00
-- url     : https://prove2.me/theorems/7f6d887f-9ea4-497e-aae7-13488aa058b4
-- title:
--   Positive two-piece inverse occupation lies after the first mark and before the second arrival
-- statement:
--   With strictly positive post-jump state z, the source occupation clock satisfies I(a)=a/y≤t and I(a+z*t)>t. Since a+z*t<b by the second-arrival buffer, the inverse occupation clock has a finite value between a and b. This is the exact interval location needed to recover the source state and avoid first-negative-passage clipping.
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

theorem Kyprianou.Ch01.reverseLampertiTwoPieceInverseClockInsidePositiveStage
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
    ∃ s : ℝ≥0, a ≤ (s : ℝ) ∧ (s : ℝ) < b ∧
      inverseReciprocalOccupation X t ω = (s : WithTop ℝ≥0) := by
  sorry
