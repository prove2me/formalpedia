-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteAffineStepActualJumpV1
-- name    : Kyprianou.Ch04.finiteAffineStepActualJumpV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:30:31.448644+00:00
-- url     : https://prove2.me/theorems/9e95c52a-c661-5ed4-9c20-04042eaaf39c
-- title:
--   Exact jumps of a finite affine step path
-- statement:
--   A local finite affine step path has the actual retained mark at each retained time, and zero jump at all other positive times.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteAffineStepActualJumpV1 (S : Finset NNReal) (j : NNReal → ℝ) (d : ℝ)
    (T : NNReal) (Y L : NNReal → ℝ)
    (hY : ∀ u ≤ T, Y u = d * (u : ℝ) + ∑ r ∈ S, if r ≤ u then j r else 0)
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u))) :
    ∀ u, 0 < u → u ≤ T → Y u - L u = if u ∈ S then j u else 0 := by
  sorry
end Kyprianou.Ch04
