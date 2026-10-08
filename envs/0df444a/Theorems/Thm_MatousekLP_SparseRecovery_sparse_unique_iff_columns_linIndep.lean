-- Prove2me | Theorems.Thm_MatousekLP_SparseRecovery_sparse_unique_iff_columns_linIndep
-- name    : MatousekLP.SparseRecovery.sparse_unique_iff_columns_linIndep
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:38:33.827501+00:00
-- url     : https://prove2.me/theorems/d115d1c3-917b-4c95-b245-bc23524df9c4
-- title:
--   Observation 8.5.1 — uniqueness of sparse solutions iff every 2r columns are independent
-- statement:
--   Fix integers $m,n,r\ge 0$ and let $A$ be a real $m\times n$ matrix. Call $x\in\mathbb{R}^n$ a sparse solution of $Ax=b$ if $Ax=b$ and $|\operatorname{supp}(x)|\le r$, where $\operatorname{supp}(x)=\{i: x_i\ne 0\}$. Then the following two conditions are equivalent:
--
--   1. for every $b\in\mathbb{R}^m$, the system $Ax=b$ has at most one sparse solution;
--   2. every $2r$ or fewer columns of $A$ are linearly independent, i.e. for every set $S$ of column indices with $|S|\le 2r$, the columns $(a_j)_{j\in S}$ are linearly independent in $\mathbb{R}^m$.
--
--   $$\bigl(\forall b\ \forall x',x''\text{ sparse solutions of }Ax=b:\ x'=x''\bigr)\iff\bigl(\forall S\subseteq\{1,\dots,n\},\ |S|\le 2r:\ (a_j)_{j\in S}\text{ linearly independent}\bigr).$$
--
--   This is the linear-algebra criterion for sparse solutions to be unique, independent of how they are computed.
--
--   **Formalization Note** Column $j$ of $A$ is `Aᵀ j`, and "every $2r$ or fewer columns" ranges over finsets of distinct column indices. Indices are $0,\dots,n-1$. At $r=0$ condition 2 is vacuous and condition 1 holds trivially, as on the page.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 168, Observation 8.5.1

import Mathlib
import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit

namespace MatousekLP.SparseRecovery

open Matrix

/-- **Observation 8.5.1**, Matoušek & Gärtner, *Understanding and Using Linear Programming*,
Springer 2007, p. 168.  With `n, m, r` fixed, for an `m × n` matrix `A` the following are
equivalent: (i) the system `Ax = b` has at most one sparse solution `x` (i.e. `Ax = b`,
`|supp(x)| ≤ r`) for every `b`; (ii) every `2r` or fewer columns of `A` are linearly
independent.  Column `j` of `A` is `Aᵀ j`. -/
theorem sparse_unique_iff_columns_linIndep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ) :
    (∀ (b : Fin m → ℝ) (x' x'' : Fin n → ℝ),
        IsSparseSolution A b r x' → IsSparseSolution A b r x'' → x' = x'') ↔
      (∀ S : Finset (Fin n), S.card ≤ 2 * r →
        LinearIndependent ℝ (fun j : S => Aᵀ (j : Fin n))) := by sorry

end MatousekLP.SparseRecovery
