-- Prove2me | Theorems.Thm_Kyprianou_Ch01_summableRealSequenceBounded
-- name    : Kyprianou.Ch01.summableRealSequenceBounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:29:11.084433+00:00
-- url     : https://prove2.me/theorems/bbb747f1-d4cc-4242-8e86-24d670e41f85
-- title:
--   Summable real sequence uniform coefficient bound
-- statement:
--   Every summable real sequence is uniformly bounded in absolute value. Apply the fact that summability implies convergence of terms to zero, which makes the range of their absolute values bounded, and take a nonnegative maximum bound.
-- source:
--   Adapted from the actual remote-Proved Lean proof AvramDividend.Classical.avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117, helper PgfAux.bdd_of_summable

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.summableRealSequenceBounded
    (a : ℕ → ℝ) (hsum : Summable a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ℕ, |a i| ≤ M := by
  sorry
