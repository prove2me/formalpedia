-- Prove2me | Theorems.Thm_Matrix_PosSemidef_exists_eq_sum_vecMulVec
-- name    : Matrix.PosSemidef.exists_eq_sum_vecMulVec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:14:59.618774+00:00
-- url     : https://prove2.me/theorems/cf1655fd-34a5-436a-9773-90c475ef1098
-- title:
--   A positive semidefinite matrix is a sum of rank-one outer products
-- statement:
--   Let $n$ be a finite index type and let $Z \in \mathbb{R}^{n \times n}$ be positive semidefinite.
--   Then $Z$ decomposes into outer products of $|n|$ vectors $z_1, \dots, z_{|n|} \in \mathbb{R}^n$:
--
--   $$
--   Z = \sum_{j} z_j z_j^{\mathsf T} .
--   $$
--
--   This is the concrete form of the square-root factorization $Z = B B^{\mathsf T}$, with the
--   columns of $B$ named explicitly, and it is the step that turns a semidefinite constraint into a
--   statement about finitely many vectors. Rank-reduction and peeling arguments for semidefinite
--   programs, and every passage from a moment matrix to a discrete measure supported on finitely
--   many atoms, begin here.
-- source:
--   S. Zymler, D. Kuhn and B. Rustem, Distributionally robust joint chance constraints with second-order moment information, Mathematical Programming 137 (2013), 167-198. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 2607-2617 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open Matrix

theorem Matrix.PosSemidef.exists_eq_sum_vecMulVec {n : Type*} [Fintype n] {Z : Matrix n n ℝ}
    (hZ : Z.PosSemidef) : ∃ z : n → n → ℝ, Z = ∑ j, vecMulVec (z j) (z j) := by sorry
