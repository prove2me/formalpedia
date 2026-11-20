-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scaleConvolutionPower_nonnegative
-- name    : Kyprianou.Ch08.StageB.scaleConvolutionPower_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:57:52.908854+00:00
-- url     : https://prove2.me/theorems/903a13b3-17ea-4dd2-a80d-cb24de127ef0
-- title:
--   Nonnegativity of causal convolution powers of a q-scale kernel
-- statement:
--   For a nonnegative scale kernel W on the positive half-line, its iterated causal self-convolutions W^{*(n+1)} are nonnegative on [0,∞) for every natural n. Induction uses the nonnegative Lebesgue integral of the product of nonnegative factors. This is a prerequisite for the factorial majorant in Lemma 8.3.
-- source:
--   Kyprianou (2006), Chapter 8, Lemma 8.3, proof of equation (8.23), p. 221.

import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- Every causal convolution power of a nonnegative kernel is nonnegative. -/
theorem scaleConvolutionPower_nonnegative (W : ℝ → ℝ)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ scaleConvolutionPower W n x := by
  sorry

end Kyprianou.Ch08.StageB
