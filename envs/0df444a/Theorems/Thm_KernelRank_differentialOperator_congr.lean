-- Prove2me | Theorems.Thm_KernelRank_differentialOperator_congr
-- name    : KernelRank.differentialOperator_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:06:53.23664+00:00
-- url     : https://prove2.me/theorems/a3f453e1-0924-4e54-8c74-6e19d43deb2d
-- title:
--   Kernel Rank: differential Operator congr
-- statement:
--   The Kernel Rank construction uses the differential Operator congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L20-L24
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L20-L24

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Differential
set_option autoImplicit true
open Polynomial NNReal
open KernelRank

theorem KernelRank.differentialOperator_congr (q : ℂ[X]) {f g : ℝ → ℂ}
    (h : Set.EqOn f g (Set.Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator q f t = differentialOperator q g t := by sorry
