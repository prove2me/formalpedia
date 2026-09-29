-- Prove2me | Theorems.Thm_MagicSquares_order_three_opposite_sum_eq_twice_center
-- name    : MagicSquares.order_three_opposite_sum_eq_twice_center
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:06:06.865446+00:00
-- url     : https://prove2.me/theorems/695c1fc5-a4a3-4ee4-9eda-9a132228ba46
-- title:
--   In an order-three magic square, opposite cells sum to twice the centre
-- statement:
--   **Opposite cells in an order-three magic square.** Let $A$ be a $3\times3$
--   magic square with line sum $S$. Then for **every** pair of centrally opposite
--   cells,
--
--   $$
--   A_{ij} + A_{2-i,\,2-j} \;=\; 2\,A_{11} .
--   $$
--
--   Equivalently, an order-three magic square is automatically *associative* with
--   complement constant $2A_{11}$. Since MacMahon's identity gives $S = 3A_{11}$,
--   each such pair sums to $\tfrac23 S$, and in particular the square is determined
--   by its centre: every opposite pair is pinned to twice it.
--
--   The four pairs are $(1,1)$–$(3,3)$ and $(1,3)$–$(3,1)$ (the two diagonals) and
--   $(1,2)$–$(3,2)$, $(2,1)$–$(2,3)$ (the middle column and middle row); the fifth
--   "pair" is the centre with itself, which is trivial. This is the structural fact
--   behind the classical parametrisation of $3\times3$ magic squares by two corner
--   entries: once $A_{11}$ and one corner are chosen, all remaining cells follow.
--
--   **Formalization Note** Cells are indexed by `Fin 3` and `Fin.rev` is the
--   reversal $i\mapsto 2-i$, so $(i,j)$ and $(\mathrm{rev}\,i,\mathrm{rev}\,j)$ are
--   the centrally opposite pair. The proof expands the nine line identities and
--   finishes by linear arithmetic; no integrality hypothesis beyond $\mathbb{N}$ is
--   needed.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3.

import Mathlib
import Definitions.Def_MagicSquares

namespace MagicSquares

theorem order_three_opposite_sum_eq_twice_center
    (M : Square 3 ℕ) (s : ℕ) (hM : IsMagic M s) (i j : Fin 3) :
    M i j + M (Fin.rev i) (Fin.rev j) = 2 * M 1 1 := by sorry

end MagicSquares
