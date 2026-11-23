-- Prove2me | Theorems.Thm_KernelRank_separableRank_ofReal
-- name    : KernelRank.separableRank_ofReal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:28:24.002748+00:00
-- url     : https://prove2.me/theorems/39b88667-1711-4479-8d6d-2577341fc589
-- title:
--   Kernel Rank: separable Rank of Real
-- statement:
--   In two coordinates, complex factors do not lower the separable rank of a real-valued kernel.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L104-L111
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Complexification.lean#L104-L111

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
set_option autoImplicit true
open KernelRank
variable {α : Type*}

theorem KernelRank.separableRank_ofReal (K : (Fin 2 → α) → ℝ) :
    separableRank (fun z => (K z : ℂ)) = separableRank K := by sorry
