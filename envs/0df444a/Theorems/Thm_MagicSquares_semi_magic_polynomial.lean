-- Prove2me | Theorems.Thm_MagicSquares_semi_magic_polynomial
-- name    : MagicSquares.semi_magic_polynomial
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-19T05:47:22.712882+00:00
-- url     : https://prove2.me/theorems/a8fa7ac8-321b-492a-9e96-d5303081a54f
-- title:
--   BCCG Theorem 1: the counting polynomial of semi-magic squares
-- statement:
--   **Goal.** For every order $n\ge 1$ there is a polynomial $p\in\mathbb{Q}[X]$ which, simultaneously, has degree exactly $(n-1)^{2}$, agrees with the counting function $H_{n}$ at every nonnegative integer, satisfies the reciprocity law $p(-n-t)=(-1)^{n-1}p(t)$ for every integer $t$, and vanishes at $-1,-2,\dots,-(n-1)$. This is Theorem 1 of Beck--Cohen--Cuomo--Gribelyuk, proved by Ehrhart and by Stanley in 1973 and given an elementary proof by Spencer in 1980. It separates the semi-magic squares from the magic, symmetric and pandiagonal classes, whose counting functions are quasi-polynomials rather than polynomials.
-- source:
--   M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013); E. Ehrhart (1973); R. P. Stanley, Duke Math. J. 40 (1973) 607--632; J. Spencer, Amer. Math. Monthly 87 (1980) 397--399; M. Beck and D. Paxton, The Ehrhart polynomial of the Birkhoff polytope (arXiv:math.CO/0202267).

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem semi_magic_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        (∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) ∧
          (∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ))
            = (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ)) ∧
            (∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0) := by
  sorry

end MagicSquares
