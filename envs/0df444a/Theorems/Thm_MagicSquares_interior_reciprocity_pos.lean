-- Prove2me | Theorems.Thm_MagicSquares_interior_reciprocity_pos
-- name    : MagicSquares.interior_reciprocity_pos
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-20T23:00:20.613543+00:00
-- url     : https://prove2.me/theorems/5ca89b06-1944-4bca-8ae9-160021073541
-- title:
--   Ehrhart-Macdonald counting reciprocity at positive dilation
-- statement:
--   **Ehrhart--Macdonald reciprocity for the Birkhoff polytope at positive dilation, in counting form.** Let $n \ge 1$ and let $p \in \mathbb{Q}[X]$ agree with the semi-magic counting function $H_{n}$ on the nonnegative integers. For every $t \ge 1$,$$p(-t) = (-1)^{(n-1)^2} I_{n}(t),$$where $I_{n}(t)$ is the number of semi-magic squares of line sum $t$ with every entry strictly positive.
--
--   The left-hand side evaluates the Ehrhart polynomial of the Birkhoff polytope $B_{n}$ (the doubly stochastic matrices, of dimension $(n-1)^2$) at the negative integer $-t$; the right-hand side counts its interior lattice points in the dilate $t \cdot B_{n}$, which are exactly the positive squares. This is the specialization of the Ehrhart--Macdonald reciprocity law to $B_{n}$, and it is the half of Stanley's argument that brings geometry into the picture: everything else in the reciprocity proof is elementary combinatorics and polynomial algebra.
--
--   The dilation must be positive: at $t = 0$ the identity is false, since $p(0) = H_{n}(0) = 1$ (the all-zero square) while $I_{n}(0) = 0$ (no entry can be positive). This restriction matches the lattice-point counts preceding the reciprocity theorem, which are introduced for positive integer dilation.
--
--   **Formalization Note** Lean states positivity through `positiveInteriorCount`, the card-of-filtered-finset interior count over `Square n (Fin (t+1))`, with the positivity hypothesis `1 ≤ t` as an explicit binder.
-- source:
--   R. P. Stanley, Duke Math. J. 40 (1973), 607--632, Ehrhart--Macdonald reciprocity applied to the Birkhoff polytope; E. Ehrhart (1973); M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
open MagicSquares

namespace MagicSquares

theorem interior_reciprocity_pos (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ t : ℕ, 1 ≤ t → p.eval (-(t : ℚ)) = (-1 : ℚ) ^ ((n - 1) ^ 2) *
      (positiveInteriorCount n t : ℚ) := by sorry

end MagicSquares
