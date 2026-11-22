-- Prove2me | Theorems.Thm_MagicSquares_birkhoff_ehrhart_small
-- name    : MagicSquares.birkhoff_ehrhart_small
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-22T09:56:48.274391+00:00
-- url     : https://prove2.me/theorems/027d082c-2003-4928-907d-3cb1612f2c95
-- title:
--   Ehrhart reciprocity for Birkhoff at small dilations
-- statement:
--   Let $n\\ge 1$ and let $p$ agree with $H_n$ on all naturals. For small positive dilations $1\\le t<n$, both sides of Ehrhart reciprocity vanish: $p(-t)=0$ and the interior count is $0$.
--
--   $$
--   p(-t)=(-1)^{(n-1)^2}\\cdot |\\{M\\in t\\cdot B_n : M_{ij}>0\\text{ and }M_{ij}\\in\\mathbb{Z}\\ \\forall i,j\\}|=0.
--   $$
--
--   The left side vanishes by the vanishing list ($p$ is zero at $-1,\\dots,-(n-1)$). The right side vanishes because a row of $n$ strictly positive entries sums to at least $n>t$: no positive integer matrix lies in the dilation. Together with the large-dilation companion, this splits Ehrhart-Macdonald reciprocity for the Birkhoff polytope into an elementary half and the remaining hard core.
--
--   **Formalization Note** The interior count uses the same `Set.ncard` expression as the full reciprocity statement, so rewriting applies directly; the only imports beyond `Mathlib` are the counting definitions and the proved vanishing theorem.
-- source:
--   R. P. Stanley, Duke Math. J. 40 (1973), 607--632 (small-dilation case of Ehrhart-Macdonald reciprocity); M. Beck et al., Amer. Math. Monthly 110 (2003), 707--717. Vanishing side: the proved vanishing list. Empty side: a row of n positive entries sums to at least n.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
open MagicSquares

namespace MagicSquares

theorem birkhoff_ehrhart_small (n : Nat) (hn : 1 <= n) (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount n t : Rat)) : forall t : Nat, 1 <= t -> t < n -> p.eval (-(t : Rat)) = (-1 : Rat) ^ ((n - 1) ^ 2) * ((Set.ncard {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = (t : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)}) : Rat) := by sorry

end MagicSquares
