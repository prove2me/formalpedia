-- Prove2me | Theorems.Thm_OAI_Release075_exists_row_basis
-- name    : OAI.Release075.exists_row_basis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:26:12.44529+00:00
-- url     : https://prove2.me/theorems/bcaa7aac-eb2c-4c50-986b-7275f72ea654
-- title:
--   A matrix has a basis of rows of size equal to its rank
-- statement:
--   Let $M$ be a matrix over a field $K$ with finite row and column index sets. Then some set of rows of $M$ is a basis of its row space: there is a finite set $S$ of row indices with
--   $$
--   |S|=\operatorname{rank}M ,
--   $$
--   such that the rows $M_i$, $i\in S$, are linearly independent and every row $M_i$ is a linear combination $\sum_{j\in S}c_jM_j$.
--
--   This is the row form of the statement that a spanning family contains a basis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L23-L54

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.exists_row_basis {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix ι κ K) :
    ∃ S : Finset ι, S.card = M.rank ∧
      LinearIndependent K (fun i : S => M i.val) ∧
      ∀ i, ∃ c : S → K, M i = ∑ j : S, c j • M j.val := by sorry
