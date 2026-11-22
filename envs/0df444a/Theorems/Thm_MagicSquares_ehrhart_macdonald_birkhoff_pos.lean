-- Prove2me | Theorems.Thm_MagicSquares_ehrhart_macdonald_birkhoff_pos
-- name    : MagicSquares.ehrhart_macdonald_birkhoff_pos
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-22T01:37:51.294954+00:00
-- url     : https://prove2.me/theorems/985f7b0a-962f-4039-804c-794f2ce86533
-- title:
--   Ehrhart-Macdonald reciprocity for the Birkhoff polytope
-- statement:
--   Let $n\ge 1$ and let $p$ be a rational polynomial with $p(t)=H_n(t)$ for every natural $t$. Then for every natural $t\ge 1$, the value of $p$ at $-t$ equals, up to the sign $(-1)^{(n-1)^2}$, the number of interior lattice points of the $t$-fold dilation of the Birkhoff polytope $B_n$.
--
--   $$
--   p(-t)=(-1)^{(n-1)^2}\cdot |\{M\in t\cdot B_n : M_{ij}>0\text{ and }M_{ij}\in\mathbb{Z}\ \forall i,j\}|.
--   $$
--
--   Here $B_n$ is the set of doubly stochastic matrices (nonnegative real matrices with all row and column sums equal to $1$), formalized as `doublyStochastic`; its vertices are the permutation matrices by the Birkhoff-von Neumann theorem, so it is an integral polytope of dimension $(n-1)^2$. Its interior lattice points in the $t$-fold dilation are exactly the strictly positive integer matrices with line sum $t$. This is the Ehrhart-Macdonald reciprocity law applied to $B_n$, due to Ehrhart and to Stanley (magic labelings of graphs). It is the geometric input of Stanley's proof: combined with the identification of the interior count with $I_n(t)$, it yields reciprocity at positive dilations.
--
--   **Formalization Note** Lean works with $\mathbb{Q}$-valued matrices and counts with `Set.ncard` (no finiteness instance needed to state it). The dilation is written with an explicit scaled witness. The hypothesis $1\le t$ is essential: at $t=0$ the left side is $p(0)=H_n(0)=1$ while the interior is empty, so the unqualified statement is false.
-- source:
--   R. P. Stanley, Linear homogeneous Diophantine equations and magic labelings of graphs, Duke Math. J. 40 (1973), 607--632, Ehrhart-Macdonald reciprocity for the Birkhoff polytope; E. Ehrhart, Sur les carres magiques, C. R. Acad. Sci. Paris 277 (1973); M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013). Mathlib: doublyStochastic, doublyStochastic_eq_convexHull_permMatrix.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
open MagicSquares

namespace MagicSquares

theorem ehrhart_macdonald_birkhoff_pos (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ) (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) : ∀ t : ℕ, 1 ≤ t → p.eval (-(t : ℚ)) = (-1 : ℚ) ^ ((n - 1) ^ 2) * (Set.ncard {M : Matrix (Fin n) (Fin n) ℚ | (∃ D, D ∈ doublyStochastic ℚ (Fin n) ∧ M = (t : ℚ) • D) ∧ ∀ i j, 0 < M i j ∧ ∃ k : ℕ, M i j = (k : ℚ)} : ℚ) := by sorry

end MagicSquares
