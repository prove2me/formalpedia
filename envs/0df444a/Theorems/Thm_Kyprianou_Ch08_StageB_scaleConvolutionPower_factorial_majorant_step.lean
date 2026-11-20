-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scaleConvolutionPower_factorial_majorant_step
-- name    : Kyprianou.Ch08.StageB.scaleConvolutionPower_factorial_majorant_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:59:10.921834+00:00
-- url     : https://prove2.me/theorems/099d2402-a0dc-4154-a65b-1c4a36c8681a
-- title:
--   Inductive step of Kyprianou convolution factorial bound (8.23)
-- statement:
--   Assuming the factorial estimate for the n-th causal self-convolution of a nonnegative monotone scale kernel, prove the n+1 bound by integrating the previous estimate over (0,x], multiplying by the monotone W and using the exact backward-power integral x^(n+1)/(n+1). This is the entire nontrivial induction step of (8.23).
-- source:
--   Kyprianou (2006), Chapter 8, Lemma 8.3 proof of equation (8.23), printed p. 221.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Transfer the n-th scale-convolution factorial bound to n+1. -/
theorem scaleConvolutionPower_factorial_majorant_step
    (W : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Set.Ici (0 : ℝ)))
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hint : IntegrableOn (fun s : ℝ => W s * scaleConvolutionPower W n (x - s))
      (Set.Ioc (0 : ℝ) x) volume)
    (hih : ∀ y : ℝ, 0 ≤ y →
      scaleConvolutionPower W n y ≤
        (y ^ n / (Nat.factorial n : ℝ)) * W y ^ (n + 1)) :
    scaleConvolutionPower W (n + 1) x ≤
      (x ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) * W x ^ (n + 2) := by
  sorry

end Kyprianou.Ch08.StageB
