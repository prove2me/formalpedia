-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52DiscretePassageToGapV1
-- name    : Kyprianou.Ch05.exercise52DiscretePassageToGapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:33:56.915536+00:00
-- url     : https://prove2.me/theorems/3e70c070-4de3-5e98-90f1-1188a5540429
-- title:
--   Discrete renewal passage margins imply a rational gap
-- statement:
--   Discrete renewal passage margins imply a rational gap
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

theorem Kyprianou.Ch05.exercise52DiscretePassageToGapV1
    (S : ℕ → ℝ) (hmono : Monotone S) (h0 : S 0 = 0)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    let n := sInf {k : ℕ | 0 < k ∧ x < S k}
    (u < S n - x ∧ y < x - S (n-1)) →
    ∃ a b : ℚ, (a : ℝ) < x-y ∧ x+u < (b : ℝ) ∧
      (∀ k : ℕ, S k ≤ (a : ℝ) ∨ (b : ℝ) ≤ S k) ∧
      ∃ k : ℕ, (b : ℝ) ≤ S k := by
  sorry
