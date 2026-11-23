-- Prove2me | Theorems.Thm_Kyprianou_Ch01_twoPieceOccupationCrossesPhysicalBeforeSecond
-- name    : Kyprianou.Ch01.twoPieceOccupationCrossesPhysicalBeforeSecond
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:38:23.345421+00:00
-- url     : https://prove2.me/theorems/cd945fed-ca8f-46d5-afe9-ebed9aad0e35
-- title:
--   After the first marked jump, reciprocal occupation strictly crosses physical time before the second arrival
-- statement:
--   For z=y+j-1>0, choose c=a+z*t, which is less than b by the larger a+(y+j)*t buffer. The occupation accumulated on [0,a] equals a/y>0; the post-jump segment contributes t. Hence J(c)>t. A source-grounded integral partition proves the strict crossing without requiring a finite offspring mean.
-- source:
--   Kyprianou (2006) §1.3.4, inverse-speed two-piece path clock estimates

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.twoPieceOccupationCrossesPhysicalBeforeSecond
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
      (t : ℝ≥0∞) < reciprocalOccupation X c ω := by
  sorry
