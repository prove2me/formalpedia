-- Prove2me | Theorems.Thm_MagicSquares_semi_magic_vanishing
-- name    : MagicSquares.semi_magic_vanishing
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-19T05:46:58.140694+00:00
-- url     : https://prove2.me/theorems/2b98befc-35ff-4cd0-be18-2536bf8adae8
-- title:
--   The vanishing list of the semi-magic counting polynomial
-- statement:
--   **The vanishing list.** Let $n\ge 1$ and let $p\in\mathbb{Q}[X]$ agree with $H_{n}$ on the nonnegative integers. Then $p$ vanishes at the negative integers $-1,-2,\dots,-(n-1)$: for every integer $k$ with $1\le k\le n-1$ we have $p(-k)=0$. This is the statement that the polytope has no interior lattice points on the relevant dilates, and it is the second identity of the goal. At $n=1$ the condition is vacuous.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013); E. Ehrhart (1973); R. P. Stanley, Duke Math. J. 40 (1973) 607--632; J. Spencer, Amer. Math. Monthly 87 (1980) 397--399; M. Beck and D. Paxton, The Ehrhart polynomial of the Birkhoff polytope (arXiv:math.CO/0202267).

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem semi_magic_vanishing (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0 := by
  sorry

end MagicSquares
