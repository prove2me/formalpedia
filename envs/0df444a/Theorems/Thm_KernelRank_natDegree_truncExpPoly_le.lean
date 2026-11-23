-- Prove2me | Theorems.Thm_KernelRank_natDegree_truncExpPoly_le
-- name    : KernelRank.natDegree_truncExpPoly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:18.025805+00:00
-- url     : https://prove2.me/theorems/d11cfc26-a4fb-4f02-81c7-9b77b76edeb3
-- title:
--   Kernel Rank: nat Degree trunc Exp Poly le
-- statement:
--   The Kernel Rank construction uses the nat Degree trunc Exp Poly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L122-L126
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L122-L126

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.natDegree_truncExpPoly_le (k : ℕ) (u : ℂ) : (truncExpPoly k u).natDegree ≤ k := by sorry
