-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoPieceClockAbsorbingJump
-- name    : Kyprianou.Ch01.reverseLampertiTwoPieceClockAbsorbingJump
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:19:05.616847+00:00
-- url     : https://prove2.me/theorems/ece08aa2-cef0-41f5-a9aa-682cf0a1bf19
-- title:
--   Extinction at first compound-Poisson mark is absorbing under the inverse-speed clock
-- statement:
--   When the first offspring shift takes a positive initial population y to zero, the reciprocal occupation integrand becomes infinite immediately after source arrival a and the inverse clock is absorbed there for physical time t≥a/y. Show that the first negative-passage truncation does not precede a, so the reverse Lamperti population is zero.
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

theorem Kyprianou.Ch01.reverseLampertiTwoPieceClockAbsorbingJump
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
    (compoundPoissonToBranching X t ω).toNat = y + j - 1 := by
  sorry
