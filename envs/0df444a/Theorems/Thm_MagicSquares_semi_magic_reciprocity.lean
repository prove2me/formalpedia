-- Prove2me | Theorems.Thm_MagicSquares_semi_magic_reciprocity
-- name    : MagicSquares.semi_magic_reciprocity
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-19T05:46:40.452229+00:00
-- url     : https://prove2.me/theorems/32ea160a-bf6c-4a8f-90f7-31289a3d3ba3
-- title:
--   Ehrhart-Macdonald reciprocity for the semi-magic counting function
-- statement:
--   **The reciprocity law.** Let $n\ge 1$ and let $p\in\mathbb{Q}[X]$ agree with $H_{n}$ on the nonnegative integers. Then $p(-n-t)=(-1)^{n-1}p(t)$ for every integer $t$. This is the reflection $t\mapsto -n-t$ of the lattice-point count, rescaled by the sign $(-1)^{n-1}$; its right-hand side counts the interior of the corresponding polytope, by the Ehrhart--Macdonald reciprocity law. The identity is not visible from the combinatorial definition of $H_{n}$, which is stated only for nonnegative $t$.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013); E. Ehrhart (1973); R. P. Stanley, Duke Math. J. 40 (1973) 607--632; J. Spencer, Amer. Math. Monthly 87 (1980) 397--399; M. Beck and D. Paxton, The Ehrhart polynomial of the Birkhoff polytope (arXiv:math.CO/0202267).

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem semi_magic_reciprocity (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ))
      = (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ) := by
  sorry

end MagicSquares
