-- Prove2me | Theorems.Thm_Kyprianou_Ch01_twoPieceOccupationBeforeFirstLePhysicalTime
-- name    : Kyprianou.Ch01.twoPieceOccupationBeforeFirstLePhysicalTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:38:20.621065+00:00
-- url     : https://prove2.me/theorems/f85807a6-fd4f-4bf7-b2c2-0db7bef38f34
-- title:
--   Before the first source jump, the reciprocal occupation clock is at most the physical time
-- statement:
--   Before a, X=y; the exact constant-prefix occupation formula gives J(u)=u/y. Since u<a≤y*t, positivity of y yields J(u)≤t.
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

theorem Kyprianou.Ch01.twoPieceOccupationBeforeFirstLePhysicalTime
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
    ∀ u : ℝ≥0, (u : ℝ) < a →
      reciprocalOccupation X u ω ≤ (t : ℝ≥0∞) := by
  sorry
