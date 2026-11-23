-- Prove2me | Theorems.Thm_KernelRank_realExpMultilinearMap_apply
-- name    : KernelRank.realExpMultilinearMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:20:29.118409+00:00
-- url     : https://prove2.me/theorems/263de23c-2591-4a6f-b396-81c33cad0ebf
-- title:
--   Kernel Rank: real Exp Multilinear Map apply
-- statement:
--   The Kernel Rank construction uses the real Exp Multilinear Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2225-L2232
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L2225-L2232

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.realExpMultilinearMap_apply {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C]
    (d : ℕ) (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_R : ι_R → ℕ) (c_C : ι_C → ℕ)
    (w_R : ι_R → ℕ → ℝ) (w_C : ι_C → ℕ → ℂ)
    (u : Fin d → RealExpSpace m_R m_C) :
    realExpMultilinearMap d m_R m_C c_R c_C w_R w_C u =
      realExpForm d m_R m_C c_R c_C w_R w_C u := by sorry
