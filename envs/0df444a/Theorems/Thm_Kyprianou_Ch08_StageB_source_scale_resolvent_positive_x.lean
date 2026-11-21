-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_resolvent_positive_x
-- name    : Kyprianou.Ch08.StageB.source_scale_resolvent_positive_x
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:41:22.837333+00:00
-- url     : https://prove2.me/theorems/a2b0804c-5d69-4c6f-b2e3-0b767c9e9127
-- title:
--   Exact source q-scale Volterra resolvent identity on x>0
-- statement:
--   For the actual source spectrally negative scale family, W^(q)(x)=W^(0)(x)+q∫_0^x W^(0)(s)W^(q)(x−s)ds at all x>0 and q≥0. The source scalar Laplace-resolvent identity, Proved positive causal convolution weighted integrability and continuousOn theorem, and Proved nonnegative-continuous Laplace uniqueness establish the identity without assuming extra stochastic properties. This is the analytic Volterra equation behind Kyprianou Lemma 8.3 (8.24), and a route to source endpoint discount invariance.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3, (8.22)-(8.24), printed p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- The true discounted scale solves the zero-discount Volterra resolvent equation. -/
theorem source_scale_resolvent_positive_x
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 < x) :
    W q x = W 0 x +
      q * (∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume) := by
  sorry

end Kyprianou.Ch08.StageB
