-- Prove2me | Theorems.Thm_KernelRank_expPolyAnnihilator_natDegree
-- name    : KernelRank.expPolyAnnihilator_natDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:07:37.670018+00:00
-- url     : https://prove2.me/theorems/bc4b9a19-47b7-4cd0-840a-c047a1627b4e
-- title:
--   Kernel Rank: exp Poly Annihilator nat Degree
-- statement:
--   The Kernel Rank construction uses the exp Poly Annihilator nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L154-L158
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L154-L158

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.expPolyAnnihilator_natDegree {ι : Type*} [Fintype ι] (P : ι → ℂ[X]) (rate : ι → ℂ) :
    (expPolyAnnihilator P rate).natDegree = ∑ i, ((P i).natDegree + 1) := by sorry
