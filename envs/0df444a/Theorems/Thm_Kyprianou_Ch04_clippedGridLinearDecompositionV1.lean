-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedGridLinearDecompositionV1
-- name    : Kyprianou.Ch04.clippedGridLinearDecompositionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:32:20.578049+00:00
-- url     : https://prove2.me/theorems/b66922c2-804e-48ae-a9b8-fddb660ced6e
-- title:
--   clippedGridLinearDecompositionV1
-- statement:
--   The clipped finite grid is linear in the state; separate a common finite-variation state.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
open scoped NNReal
set_option autoImplicit false

/-- Linearity splits the difference of two clipped state grids into their common
finite-variation grid and their respective compensated small-jump grids. -/

theorem Kyprianou.Ch04.clippedGridLinearDecompositionV1 (Y Z V H L : NNReal → ℝ) (u : ℕ → NNReal) (n : ℕ) (t : NNReal) :
    let G := fun (X W : NNReal → ℝ) =>
      ∑ k ∈ Finset.range n, W (u k) * (X (min t (u (k+1)))-X (min t (u k)))
    G Y H - G Z L = (G V H - G V L) +
      (G (fun s => Y s-V s) H - G (fun s => Z s-V s) L) := by
  sorry
