-- Prove2me | Theorems.Thm_MatousekLP_SparseRecovery_two_r_le_m
-- name    : MatousekLP.SparseRecovery.two_r_le_m
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:38:43.307589+00:00
-- url     : https://prove2.me/theorems/f04b7dbe-969b-4bef-a940-7479b9bfae61
-- title:
--   §8.5, p. 169 — condition (ii) of Observation 8.5.1 forces m ≥ 2r
-- statement:
--   Let $A$ be a real $m\times n$ matrix with $m<n$ (the standing assumption of the sparse-solution problem in §8.5), and let $r\ge 0$ be an integer. Suppose every $2r$ or fewer columns of $A$ are linearly independent (condition (ii) of Observation 8.5.1). Then
--   $$m\ \ge\ 2r .$$
--
--   Combined with Observation 8.5.1, this says that uniqueness of $r$-sparse solutions requires at least $2r$ equations.
--
--   **Formalization Note** Column $j$ of $A$ is `Aᵀ j`; the hypothesis $m<n$ is the book's standing assumption on page 168 ("an $m\times n$ matrix $A$ with $m<n$"), without which the claim fails (e.g. $m=n=1$, $A=(1)$, $r=1$).
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 169, §8.5 (remark after Observation 8.5.1: "(ii) implies that, in particular, m ≥ 2r"); standing assumption m < n from the box on p. 168

import Mathlib
import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit

namespace MatousekLP.SparseRecovery

open Matrix

/-- **§8.5, p. 169** (remark after Observation 8.5.1), Matoušek & Gärtner, *Understanding and
Using Linear Programming*, Springer 2007: "(ii) implies that, in particular, `m ≥ 2r`".
Condition (ii) of Observation 8.5.1 says that every `2r` or fewer columns of the `m × n` matrix
`A` are linearly independent.  The standing assumption `m < n` of §8.5 (p. 168, "an `m × n`
matrix `A` with `m < n`") is a hypothesis. -/
theorem two_r_le_m {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ) (hmn : m < n)
    (hii : ∀ S : Finset (Fin n), S.card ≤ 2 * r →
      LinearIndependent ℝ (fun j : S => Aᵀ (j : Fin n))) :
    2 * r ≤ m := by sorry

end MatousekLP.SparseRecovery
