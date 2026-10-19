-- Prove2me | Theorems.Thm_OAI_Release075_pow_card_sub_rank_dvd_det
-- name    : OAI.Release075.pow_card_sub_rank_dvd_det
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:28:18.227144+00:00
-- url     : https://prove2.me/theorems/ce9dc267-3488-4b9c-8e3a-dd0a93295730
-- title:
--   Rank loss modulo a prime divides the determinant
-- statement:
--   Let $A$ be a square integer matrix indexed by a finite set $\iota$ and let $q$ be a prime. Write $\bar A$ for the reduction of $A$ modulo $q$, a matrix over $\mathbb Z/q$. Then
--   $$
--   q^{\,|\iota|-\operatorname{rank}\bar A}\ \Big|\ \det A .
--   $$
--
--   In particular, if $\det A\ne0$ and $|\det A|$ is small compared with $q$, the reduction cannot lose much rank.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L83-L126

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.pow_card_sub_rank_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (q : ℕ) [Fact q.Prime] :
    (q : ℤ) ^ (Fintype.card ι - (A.map (Int.cast : ℤ → ZMod q)).rank) ∣ A.det := by sorry
