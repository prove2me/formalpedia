-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceClockPositiveJump
-- name    : Kyprianou.Ch01.reverseLampertiTwoPieceClockPositiveJump
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:19:04.435893+00:00
-- url     : https://prove2.me/theorems/24b480e7-b112-47c0-9540-35d2c93f08f5
-- title:
--   Positive post-first population is recovered by the two-piece inverse occupation clock
-- statement:
--   When the post-first population z=y+j-1 is strictly positive, the inverse-speed integral up to source time s in [a,b) is a/y+(s-a)/z. The physical clock t is at least a/y, while b>a+(y+j)t guarantees that the inverse crossing occurs strictly before b. The source stays at z there, and the first negative-passage cut-off cannot intervene.
-- source:
--   Kyprianou (2006) §1.3.4, inverse Lamperti two-piece clock

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiTwoPieceClockPositiveJump
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
    (compoundPoissonToBranching X t ω).toNat = y + j - 1 := by
  sorry
