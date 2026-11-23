-- Prove2me | Theorems.Thm_KernelRank_coeff_prod_truncExpPoly
-- name    : KernelRank.coeff_prod_truncExpPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:08:28.38653+00:00
-- url     : https://prove2.me/theorems/9e4d011d-0d48-4227-9ad9-ac7da59548c9
-- title:
--   Kernel Rank: coeff prod trunc Exp Poly
-- statement:
--   The Kernel Rank construction uses the coeff prod trunc Exp Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L128-L160
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L128-L160

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.coeff_prod_truncExpPoly {α : Type*} (S : Finset α) (k : ℕ) (u : α → ℂ)
    {q : ℕ} (hq : q ≤ k) :
    (∏ j ∈ S, truncExpPoly k (u j)).coeff q =
      (∑ j ∈ S, u j) ^ q / (q.factorial : ℂ) := by sorry
