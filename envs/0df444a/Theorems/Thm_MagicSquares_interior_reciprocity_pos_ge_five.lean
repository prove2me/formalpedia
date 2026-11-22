-- Prove2me | Theorems.Thm_MagicSquares_interior_reciprocity_pos_ge_five
-- name    : MagicSquares.interior_reciprocity_pos_ge_five
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-22T01:08:34.349988+00:00
-- url     : https://prove2.me/theorems/43ccc9fe-b78d-4f6f-b5e1-a86cd21af25f
-- title:
--   Positive Ehrhart-Macdonald reciprocity for n at least five
-- statement:
--   Let $n\\ge 5$ and let $p$ be a rational polynomial agreeing with the semi-magic counting function $H_n$ at every natural number. Then for every natural $s\\ge n$, the value of $p$ at $-s$ equals, up to the sign $(-1)^{(n-1)^2}$, the number $I_n(s)$ of positive semi-magic squares of line sum $s$.
--
--   $$
--   p(-s)=(-1)^{(n-1)^2}I_n(s).
--   $$
--
--   Here $H_n(t)$ counts $n\\times n$ arrays of nonnegative integers with all row and column sums equal to $t$, and $I_n(s)$ counts those with every entry at least one. Geometrically, $I_n(s)$ is the number of interior lattice points of the $s$-fold dilation of the Birkhoff polytope $B_n$, so this is the Ehrhart-Macdonald reciprocity law for $B_n$ evaluated at positive dilations, specialized to orders $n\\ge 5$. Combined with the elementary shift bijection $I_n(n+u)=H_n(u)$ it yields the functional equation $p(-n-u)=(-1)^{(n-1)^2}p(u)$ for every natural $u$.
--
--   **Formalization Note** Lean counts via `semiMagicCount` and `positiveInteriorCount` over arrays with entries in `Fin (t+1)`, and evaluates $p$ at rationals via casts; the hypothesis is $5\\le n$ rather than $1\\le n$.
-- source:
--   R. P. Stanley, Linear homogeneous Diophantine equations and magic labelings of graphs, Duke Math. J. 40 (1973), 607--632, Ehrhart-Macdonald reciprocity for the Birkhoff polytope; M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, The number of magic squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013), specialized to n >= 5 and positive dilations s >= n.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
open MagicSquares

namespace MagicSquares

theorem interior_reciprocity_pos_ge_five (n : Nat) (hn : 5 <= n) (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount n t : Rat)) : forall s : Nat, n <= s -> p.eval (-(s : Rat)) = (-1 : Rat) ^ ((n - 1) ^ 2) * (positiveInteriorCount n s : Rat) := by sorry

end MagicSquares
