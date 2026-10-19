-- Prove2me | Theorems.Thm_OAI_Release075_exists_full_rank_minor
-- name    : OAI.Release075.exists_full_rank_minor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:28:49.090978+00:00
-- url     : https://prove2.me/theorems/106a0769-0908-4131-aacd-e4e9c742643c
-- title:
--   A matrix has a nonsingular square minor of size its rank
-- statement:
--   Let $M$ be a matrix over a field $K$ with finite row and column index sets, and let $k=\operatorname{rank}M$. Then there are injective maps $f:\{0,\dots,k-1\}\to$ rows and $g:\{0,\dots,k-1\}\to$ columns such that the $k\times k$ minor is nonsingular:
--   $$
--   \det\bigl(M_{f(a),g(b)}\bigr)_{a,b<k}\ne0 .
--   $$
--
--   So the rank is attained by a square submatrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L128-L150

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.exists_full_rank_minor {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix ι κ K) :
    ∃ (f : Fin M.rank → ι) (g : Fin M.rank → κ),
      Function.Injective f ∧ Function.Injective g ∧ (M.submatrix f g).det ≠ 0 := by sorry
