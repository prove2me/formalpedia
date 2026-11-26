-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52DiscreteRenewalGapV1
-- name    : Kyprianou.Ch05.exercise52DiscreteRenewalGapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:31:53.446625+00:00
-- url     : https://prove2.me/theorems/2f431483-5a09-448c-ab0d-efe314ab75f7
-- title:
--   For a nondecreasing renewal sequence the two strict margins equal avoidance of a rational gap
-- statement:
--   For a nondecreasing renewal sequence the two strict margins equal avoidance of a rational gap
-- source:
--   Kyprianou (2006), Exercise 5.2(ii)

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05

theorem Kyprianou.Ch05.exercise52DiscreteRenewalGapV1
    (S : ℕ → ℝ) (hmono : Monotone S) (h0 : S 0 = 0)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    let n := sInf {k : ℕ | 0 < k ∧ x < S k}
    (u < S n - x ∧ y < x - S (n-1)) ↔
    ∃ a b : ℚ, (a : ℝ) < x-y ∧ x+u < (b : ℝ) ∧
      (∀ k : ℕ, S k ≤ (a : ℝ) ∨ (b : ℝ) ≤ S k) ∧
      ∃ k : ℕ, (b : ℝ) ≤ S k := by
  sorry
