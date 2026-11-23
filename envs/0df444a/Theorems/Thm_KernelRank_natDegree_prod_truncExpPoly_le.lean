-- Prove2me | Theorems.Thm_KernelRank_natDegree_prod_truncExpPoly_le
-- name    : KernelRank.natDegree_prod_truncExpPoly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:12.591206+00:00
-- url     : https://prove2.me/theorems/5c4b32db-e353-4832-a63d-317e48b1afdd
-- title:
--   Kernel Rank: nat Degree prod trunc Exp Poly le
-- statement:
--   The Kernel Rank construction uses the nat Degree prod trunc Exp Poly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L162-L169
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L162-L169

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.natDegree_prod_truncExpPoly_le {α : Type*} (S : Finset α) (k : ℕ) (u : α → ℂ) :
    (∏ j ∈ S, truncExpPoly k (u j)).natDegree ≤ S.card * k := by sorry
