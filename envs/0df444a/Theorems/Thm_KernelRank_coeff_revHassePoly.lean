-- Prove2me | Theorems.Thm_KernelRank_coeff_revHassePoly
-- name    : KernelRank.coeff_revHassePoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:13:02.63048+00:00
-- url     : https://prove2.me/theorems/a57a539f-c0a3-4689-b443-b81b0e80e87c
-- title:
--   Kernel Rank: coeff rev Hasse Poly
-- statement:
--   The Kernel Rank construction uses the coeff rev Hasse Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L176-L188
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L176-L188

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.coeff_revHassePoly (P : ℂ[X]) (k : ℕ) (u : ℂ) {n : ℕ} (hn : n ≤ k) :
    (revHassePoly P k u).coeff n =
      ((k - n).factorial : ℂ) * (hasseDeriv (k - n) P).eval u := by sorry
