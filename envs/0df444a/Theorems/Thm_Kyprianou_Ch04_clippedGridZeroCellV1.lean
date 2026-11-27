-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedGridZeroCellV1
-- name    : Kyprianou.Ch04.clippedGridZeroCellV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:55:07.686473+00:00
-- url     : https://prove2.me/theorems/858e7ed5-ac9e-5772-920e-f0333745836e
-- title:
--   clippedGridZeroCellV1
-- statement:
--   clippedGridZeroCellV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), physical clipped-grid uniform cutoff estimate

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.clippedGridZeroCellV1
    (Y H : NNReal → ℝ) (u : ℕ → NNReal) (n : ℕ) (t : NNReal)
    (hn : 0 < n) (h0 : u 0 = 0)
    (hp : ∀ k ∈ Finset.range n, k ≠ 0 → 0 < u k) :
    (∑ k ∈ Finset.range n, H (u k) * (Y (min t (u (k+1))) - Y (min t (u k)))) -
      (∑ k ∈ Finset.range n, (if u k = 0 then 0 else H (u k)) *
        (Y (min t (u (k+1))) - Y (min t (u k)))) =
      H 0 * (Y (min t (u 1)) - Y 0) := by
  sorry
