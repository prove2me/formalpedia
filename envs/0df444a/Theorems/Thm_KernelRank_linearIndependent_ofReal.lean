-- Prove2me | Theorems.Thm_KernelRank_linearIndependent_ofReal
-- name    : KernelRank.linearIndependent_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:57:04.318855+00:00
-- url     : https://prove2.me/theorems/52b365d5-915b-4d1b-8f40-ebfe12273a05
-- title:
--   Kernel Rank: linear Independent of Real
-- statement:
--   Real linearly independent functions remain independent over the complex numbers.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L17-L31
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L17-L31

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
set_option autoImplicit true
open KernelRank

theorem KernelRank.linearIndependent_ofReal {α ι : Type*} {f : ι → α → ℝ} (hf : LinearIndependent ℝ f) :
    LinearIndependent ℂ (fun i x => (f i x : ℂ)) := by sorry
