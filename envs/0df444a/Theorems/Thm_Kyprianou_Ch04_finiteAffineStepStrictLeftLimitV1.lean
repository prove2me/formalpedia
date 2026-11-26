-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteAffineStepStrictLeftLimitV1
-- name    : Kyprianou.Ch04.finiteAffineStepStrictLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:28:53.701103+00:00
-- url     : https://prove2.me/theorems/918ce52e-068b-41c7-9a0a-63098a557823
-- title:
--   Strict left limit of a local finite affine step path
-- statement:
--   The strict left limit of a locally affine finite step path is the strict jump sum.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteAffineStepStrictLeftLimitV1 (S : Finset NNReal) (j : NNReal → ℝ) (d : ℝ)
    (T : NNReal) (Y L : NNReal → ℝ)
    (hY : ∀ u ≤ T, Y u = d * (u : ℝ) + ∑ r ∈ S, if r ≤ u then j r else 0)
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u))) :
    ∀ u, 0 < u → u ≤ T →
      L u = d * (u : ℝ) + ∑ r ∈ S, if r < u then j r else 0 := by
  sorry
end Kyprianou.Ch04
