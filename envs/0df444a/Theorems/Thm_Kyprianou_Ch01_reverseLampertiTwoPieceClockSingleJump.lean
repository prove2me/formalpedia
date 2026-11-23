-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceClockSingleJump
-- name    : Kyprianou.Ch01.reverseLampertiTwoPieceClockSingleJump
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:13:47.66206+00:00
-- url     : https://prove2.me/theorems/e04a784f-5925-49ab-a4b0-00079e53511b
-- title:
--   Deterministic inverse-speed clock and first-jump population before a second source arrival
-- statement:
--   A nonnegative initial integer y and one offspring-shift jump j-1 produce a two-piece nonnegative source path: y until time a, then y+j-1 until b. If a≤y*t and b>a+(y+j)*t, the inverse reciprocal occupation clock at physical time t lies in the post-first-jump stage and strictly before b, or is absorbed at zero if y+j-1=0. Hence the inverse Lamperti population is y+j-1. The proof must handle extinction and first-negative-passage clipping, as well as a potential infinite inverse-speed integral.
-- source:
--   Kyprianou (2006) §1.3.4, two-piece inverse Lamperti occupation clock

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiTwoPieceClockSingleJump
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y j : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (a b : ℝ) (ha : 0 < a)
    (hAB : a < b)
    (hPrefix : ∀ u : ℝ≥0, (u : ℝ) < a →
      X u ω = (y : ℤ))
    (hMiddle : ∀ u : ℝ≥0, a ≤ (u : ℝ) →
      (u : ℝ) < b → X u ω = ((y + j - 1 : ℕ) : ℤ))
    (hFirst : a ≤ (y : ℝ) * (t : ℝ))
    (hSecond : a + ((y + j : ℕ) : ℝ) * (t : ℝ) < b) :
    (compoundPoissonToBranching X t ω).toNat = y + j - 1 := by
  sorry
