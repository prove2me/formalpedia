-- Prove2me | Theorems.Thm_KernelRank_coeff_truncExpPoly
-- name    : KernelRank.coeff_truncExpPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:08:59.221839+00:00
-- url     : https://prove2.me/theorems/422b9bca-8915-41e2-98c4-d86e9f33db7d
-- title:
--   Kernel Rank: coeff trunc Exp Poly
-- statement:
--   The Kernel Rank construction uses the coeff trunc Exp Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L116-L120
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L116-L120

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.coeff_truncExpPoly (k : ℕ) (u : ℂ) (q : ℕ) :
    (truncExpPoly k u).coeff q = if q ≤ k then u ^ q / (q.factorial : ℂ) else 0 := by sorry
