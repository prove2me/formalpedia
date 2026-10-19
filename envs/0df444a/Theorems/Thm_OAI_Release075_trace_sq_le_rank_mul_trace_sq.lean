-- Prove2me | Theorems.Thm_OAI_Release075_trace_sq_le_rank_mul_trace_sq
-- name    : OAI.Release075.trace_sq_le_rank_mul_trace_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:31:47.742226+00:00
-- url     : https://prove2.me/theorems/0d1f5239-4239-4313-9c05-ddc8db2f5a2d
-- title:
--   The trace–rank inequality for real symmetric matrices
-- statement:
--   Let $A$ be a real symmetric (Hermitian) square matrix with finite index set. Then
--   $$
--   (\operatorname{tr}A)^2\le\operatorname{rank}(A)\cdot\operatorname{tr}(A^2).
--   $$
--
--   This lower-bounds the rank by $(\operatorname{tr}A)^2/\operatorname{tr}(A^2)$. It is applied to Gram matrices in the finite quotient.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L235-L257

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.trace_sq_le_rank_mul_trace_sq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ (A.rank : ℝ) * (A * A).trace := by sorry
