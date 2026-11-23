-- Prove2me | Theorems.Thm_KernelRank_IsSumOfProducts_comp
-- name    : KernelRank.IsSumOfProducts.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:48:27.233657+00:00
-- url     : https://prove2.me/theorems/fd87eb22-9d64-40b5-914b-25d5b3e7ab6f
-- title:
--   Is Sum Of Products: comp
-- statement:
--   The Is Sum Of Products construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L34-L39
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L34-L39

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.IsSumOfProducts.comp {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X Y : ι → Type*} {K : (∀ i, X i) → 𝕜} {N : ℕ} (hK : IsSumOfProducts K N)
    (g : ∀ i, Y i → X i) :
    IsSumOfProducts (fun y => K fun i => g i (y i)) N := by sorry
