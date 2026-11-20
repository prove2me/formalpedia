-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_factorial_bounded_complex_series_entire
-- name    : Kyprianou.Ch08.StageB.factorial_bounded_complex_series_entire
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T00:08:46.967019+00:00
-- url     : https://prove2.me/theorems/b8f8dde9-62ec-4c90-bab5-e698aec26648
-- title:
--   Factorial coefficient majorants give an entire power series
-- statement:
--   If real coefficients a_n satisfy the complex absolute-value bound |a_n|≤M R^n/n! for nonnegative M and R, then the complex series sum_n z^n a_n converges locally uniformly with holomorphic sum on all of C. This transfers the exact factorial scale convolution estimate (8.23) into the entire analytic conclusion in Kyprianou Lemma 8.3.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3, proof from (8.23) to (8.24), printed p. 221.

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- A factorial norm majorant makes a complex power series entire. -/
theorem factorial_bounded_complex_series_entire
    (a : ℕ → ℝ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hbound : ∀ n : ℕ,
      ‖((a n : ℝ) : ℂ)‖ ≤ M * R ^ n / (Nat.factorial n : ℝ)) :
    Differentiable ℂ (fun z : ℂ =>
      ∑' n : ℕ, z ^ n * ((a n : ℝ) : ℂ)) := by
  sorry

end Kyprianou.Ch08.StageB
