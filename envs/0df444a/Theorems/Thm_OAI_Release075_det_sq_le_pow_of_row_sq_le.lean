-- Prove2me | Theorems.Thm_OAI_Release075_det_sq_le_pow_of_row_sq_le
-- name    : OAI.Release075.det_sq_le_pow_of_row_sq_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:29:27.065258+00:00
-- url     : https://prove2.me/theorems/4711e087-e500-49b5-805c-af27d08b6fef
-- title:
--   Squared Hadamard inequality with a uniform row bound
-- statement:
--   Let $A$ be a real $n\times n$ matrix and $r\in\mathbb R$ such that every row has squared Euclidean norm at most $r$, i.e. $\sum_jA_{ij}^2\le r$ for all $i$. Then
--   $$
--   (\det A)^2\le r^{\,n}.
--   $$
--
--   This is Hadamard's inequality, squared to avoid square roots.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L152-L168

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.det_sq_le_pow_of_row_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ r) : A.det ^ 2 ≤ r ^ n := by sorry
