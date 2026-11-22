-- Prove2me | Theorems.Thm_MagicSquares_birkhoff_interior_count_eq_positive
-- name    : MagicSquares.birkhoff_interior_count_eq_positive
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-22T01:37:42.47765+00:00
-- url     : https://prove2.me/theorems/58dd1ece-3454-49e7-9ba7-f65dc691aa63
-- title:
--   Interior lattice points of Birkhoff dilates are positive squares
-- statement:
--   Let $n\ge 1$. For every natural $t$, the number of interior lattice points of the $t$-fold dilation of the Birkhoff polytope $B_n$ equals the number $I_n(t)$ of positive semi-magic squares of line sum $t$.
--
--   $$
--   |\{M\in t\cdot B_n : M_{ij}>0\text{ and }M_{ij}\in\mathbb{Z}\ \forall i,j\}|=I_n(t).
--   $$
--
--   An interior lattice point is a rational matrix in the scaled doubly stochastic set with strictly positive integer entries. Writing such a matrix as $t$ times a doubly stochastic matrix, every entry of the latter lies in $[0,1]$, so every entry of the former lies in $[0,t]$ and the $\mathrm{Fin}\, (t+1)$ bound used by the counting functions is lossless. The line sums are preserved by the scaling. This is the combinatorial bridge of Stanley's argument: it lets the Ehrhart output feed the elementary shift bijection $I_n(n+u)=H_n(u)$. Both sides vanish for $t<n$ (a row of $n$ positive entries sums to at least $n$), so no side condition on $t$ is needed.
--
--   **Formalization Note** Lean counts the left side with `Set.ncard` over $\mathbb{Q}$-matrices and the right side with `positiveInteriorCount` over `Square n (Fin (t+1))`; the hypothesis $1\le n$ matches the shift and vanishing lemmas.
-- source:
--   R. P. Stanley, Duke Math. J. 40 (1973), 607--632 (interior lattice points of dilates of the Birkhoff polytope are positive magic labelings); Mathlib: le_one_of_mem_doublyStochastic, exists_mem_doublyStochastic_eq_smul_iff; platform precedent: positive_shift_count (bijection shifting by the all-ones matrix).

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
open MagicSquares

namespace MagicSquares

theorem birkhoff_interior_count_eq_positive (n : ℕ) (hn : 1 ≤ n) : ∀ t : ℕ, Set.ncard {M : Matrix (Fin n) (Fin n) ℚ | (∃ D, D ∈ doublyStochastic ℚ (Fin n) ∧ M = (t : ℚ) • D) ∧ ∀ i j, 0 < M i j ∧ ∃ k : ℕ, M i j = (k : ℚ)} = positiveInteriorCount n t := by sorry

end MagicSquares
