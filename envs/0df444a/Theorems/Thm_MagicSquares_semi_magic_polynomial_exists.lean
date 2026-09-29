-- Prove2me | Theorems.Thm_MagicSquares_semi_magic_polynomial_exists
-- name    : MagicSquares.semi_magic_polynomial_exists
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-19T05:46:22.493778+00:00
-- url     : https://prove2.me/theorems/3dc34529-feed-4b21-bd4f-443097422b63
-- title:
--   The counting function of semi-magic squares is a polynomial
-- statement:
--   **Existence and degree, uniformly in the order.** For every $n\ge 1$ there is a polynomial $p\in\mathbb{Q}[X]$, of degree exactly $(n-1)^{2}$, whose value at each nonnegative integer $t$ is the number $H_{n}(t)$ of $n\times n$ semi-magic squares of line sum $t$. The degree $(n-1)^{2}$ is the dimension of the Birkhoff polytope $B_{n}$, and the integrality of its vertices is what makes the period one, so that the counting function is a polynomial and not merely a quasi-polynomial. This is the first half of the goal, isolated so that it can be attacked on its own.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013); E. Ehrhart (1973); R. P. Stanley, Duke Math. J. 40 (1973) 607--632; J. Spencer, Amer. Math. Monthly 87 (1980) 397--399; M. Beck and D. Paxton, The Ehrhart polynomial of the Birkhoff polytope (arXiv:math.CO/0202267).

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem semi_magic_polynomial_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  sorry

end MagicSquares
