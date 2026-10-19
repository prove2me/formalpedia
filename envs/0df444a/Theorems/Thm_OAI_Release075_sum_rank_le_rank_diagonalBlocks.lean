-- Prove2me | Theorems.Thm_OAI_Release075_sum_rank_le_rank_diagonalBlocks
-- name    : OAI.Release075.sum_rank_le_rank_diagonalBlocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:33:15.195856+00:00
-- url     : https://prove2.me/theorems/f809ea83-ca2b-4ff4-aa93-9f8b249c09cd
-- title:
--   Rank of a block-diagonal matrix bounds the sum of block ranks
-- statement:
--   Let $(Y_i)_{i\in I}$ be a finite family of matrices of the same shape $\iota\times\kappa$ over a field $K$, and let $\operatorname{diag}(Y)$ be the block-diagonal matrix indexed by $I\times\iota$ and $I\times\kappa$ with blocks $Y_i$. Then
--   $$
--   \sum_{i\in I}\operatorname{rank}Y_i\le\operatorname{rank}\operatorname{diag}(Y).
--   $$
--
--   (Equality holds, but only this inequality is stated.)
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L463-L489

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.sum_rank_le_rank_diagonalBlocks {I ι κ K : Type*} [Fintype I]
    [Fintype ι] [Fintype κ] [DecidableEq I] [Field K]
    (Y : I → Matrix ι κ K) : (∑ i, (Y i).rank) ≤ (diagonalBlocks Y).rank := by sorry
