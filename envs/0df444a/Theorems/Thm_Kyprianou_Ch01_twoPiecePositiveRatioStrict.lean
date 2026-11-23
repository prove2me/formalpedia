-- Prove2me | Theorems.Thm_Kyprianou_Ch01_twoPiecePositiveRatioStrict
-- name    : Kyprianou.Ch01.twoPiecePositiveRatioStrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:50:48.042966+00:00
-- url     : https://prove2.me/theorems/3202793a-e68b-47b1-bc20-3ec4b4085597
-- title:
--   Positive offspring-shift clock ratio exceeds physical time by one source-rate unit
-- statement:
--   For y>0, z=y+j-1>0 and t>0, z<y+j. Multiply this strict Nat comparison first by finite positive t, then by reciprocal z, and cancel reciprocal z times z to obtain t<(y+j)*t/z in ENNReal. This is entirely elementary ordered ENNReal multiplication.
-- source:
--   Kyprianou (2006) §1.3.4 inverse Lamperti post-mark occupation

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.twoPiecePositiveRatioStrict
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
    0 < t →
    (t : ℝ≥0∞) <
      (1 / ((y + j - 1 : ℕ) : ℝ≥0∞)) *
        (((y + j : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)) := by
  sorry
