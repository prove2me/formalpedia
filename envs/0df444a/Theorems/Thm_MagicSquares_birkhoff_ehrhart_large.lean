-- Prove2me | Theorems.Thm_MagicSquares_birkhoff_ehrhart_large
-- name    : MagicSquares.birkhoff_ehrhart_large
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-22T09:56:50.221726+00:00
-- url     : https://prove2.me/theorems/eadd60e3-e65e-4210-bf01-40403ce97746
-- title:
--   Ehrhart reciprocity for Birkhoff at large dilations
-- statement:
--   Let $n\\ge 1$ and let $p$ agree with $H_n$ on all naturals. For large dilations $t\\ge n$, Ehrhart-Macdonald reciprocity holds at $t$:
--
--   $$
--   p(-t)=(-1)^{(n-1)^2}\\cdot |\\{M\\in t\\cdot B_n : M_{ij}>0\\text{ and }M_{ij}\\in\\mathbb{Z}\\ \\forall i,j\\}|.
--   $$
--
--   This is the hard core of reciprocity for the Birkhoff polytope $B_n$ in interior-count form: the small-dilation companion (both sides zero) is elementary, while this case carries the full content of Stanley's reciprocity law. It is the `Set.ncard` counterpart of the functional-equation family; the proved identification of the interior count with $I_n$ translates between the two forms.
--
--   **Formalization Note** Same `Set.ncard` expression as the full statement, so the split-and-recombine sketch rewrites directly. Provable from Ehrhart theory (Hilbert series of the Birkhoff monoid); do not import the functional-equation theorems, which depend on this circle transitively.
-- source:
--   R. P. Stanley, Linear homogeneous Diophantine equations and magic labelings of graphs, Duke Math. J. 40 (1973), 607--632, Ehrhart-Macdonald reciprocity for the Birkhoff polytope at large dilations; M. Beck et al., Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
open MagicSquares

namespace MagicSquares

theorem birkhoff_ehrhart_large (n : Nat) (hn : 1 <= n) (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount n t : Rat)) : forall t : Nat, n <= t -> p.eval (-(t : Rat)) = (-1 : Rat) ^ ((n - 1) ^ 2) * ((Set.ncard {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = (t : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)}) : Rat) := by sorry

end MagicSquares
