-- Prove2me | Theorems.Thm_OAI_Release075_pow_sub_card_dvd_det
-- name    : OAI.Release075.pow_sub_card_dvd_det
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:26:42.874618+00:00
-- url     : https://prove2.me/theorems/afd08ac7-11ef-4414-985a-e1c60b078913
-- title:
--   Rows divisible by q contribute powers of q to the determinant
-- statement:
--   Let $A$ be a square integer matrix indexed by a finite set $\iota$, let $S\subseteq\iota$, and let $q\in\mathbb Z$. If every entry of every row outside $S$ is divisible by $q$, then
--   $$
--   q^{\,|\iota|-|S|}\ \Big|\ \det A .
--   $$
--
--   Each of the $|\iota|-|S|$ divisible rows contributes one factor $q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L56-L81

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.pow_sub_card_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (S : Finset ι) (q : ℤ)
    (h : ∀ i, i ∉ S → ∀ j, q ∣ A i j) :
    q ^ (Fintype.card ι - S.card) ∣ A.det := by sorry
