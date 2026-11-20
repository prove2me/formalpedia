-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scale_causal_integrand_upper
-- name    : Kyprianou.Ch08.StageB.scale_causal_integrand_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:45:40.136389+00:00
-- url     : https://prove2.me/theorems/94675bfb-c36c-401d-8c22-836bc5be59fe
-- title:
--   Scale-function causal-convolution integrand bound
-- statement:
--   For a nonnegative, nondecreasing scale function W on the positive half-line and 0≤s≤x, the product W(s)W(x−s) is bounded by W(x)^2. This is the pointwise integrand bound needed for the first step of the factorial convolution-power estimate in Lemma 8.3.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3 proof of (8.23), printed p. 221.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- Pointwise integrand bound for the first scale-convolution power. -/
theorem scale_causal_integrand_upper (W : ℝ → ℝ)
    (hmono : MonotoneOn W (Set.Ici (0 : ℝ)))
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ W t)
    (x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) (hsx : s ≤ x) :
    W s * W (x - s) ≤ (W x) ^ 2 := by
  sorry

end Kyprianou.Ch08.StageB
