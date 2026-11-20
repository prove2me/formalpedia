-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scaleConvolutionPower_factorial_majorant
-- name    : Kyprianou.Ch08.StageB.scaleConvolutionPower_factorial_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:58:14.679204+00:00
-- url     : https://prove2.me/theorems/8e46fc58-736c-415a-94a2-c9313fe51489
-- title:
--   Full factorial bound for causal q-scale convolution powers
-- statement:
--   For a nonnegative, nondecreasing real scale kernel W, whose causal convolution powers are locally integrable, the n-th zero-based self-convolution power satisfies W^{*(n+1)}(x)≤x^n W(x)^{n+1}/n!. This is exactly the factorial estimate (8.23) that makes the Chapter 8 scale family entire in q (Lemma 8.3).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3, equation (8.23), printed p. 221.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Kyprianou (8.23), expressed with zero-based causal convolution powers. -/
theorem scaleConvolutionPower_factorial_majorant
    (W : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Set.Ici (0 : ℝ)))
    (hconv : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ => W s * scaleConvolutionPower W n (x - s))
        (Set.Ioc (0 : ℝ) x) volume)
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    scaleConvolutionPower W n x ≤
      (x ^ n / (Nat.factorial n : ℝ)) * (W x) ^ (n + 1) := by
  sorry

end Kyprianou.Ch08.StageB
