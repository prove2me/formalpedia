-- Prove2me | Theorems.Thm_KernelRank_IsSumOfProducts_finsetSum
-- name    : KernelRank.IsSumOfProducts.finsetSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:48:53.658438+00:00
-- url     : https://prove2.me/theorems/ceca2ebf-7d35-46ba-8212-444dbbcde127
-- title:
--   Is Sum Of Products: finset Sum
-- statement:
--   The Is Sum Of Products construction uses the finset Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L41-L51
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L41-L51

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.IsSumOfProducts.finsetSum {𝕜 : Type*} [CommSemiring 𝕜] {ι α : Type*} [Fintype ι]
    [Fintype α] {X : ι → Type*} {K : α → (∀ i, X i) → 𝕜} {N : α → ℕ}
    (hK : ∀ a, IsSumOfProducts (K a) (N a)) :
    IsSumOfProducts (fun x => ∑ a, K a x) (∑ a, N a) := by sorry
