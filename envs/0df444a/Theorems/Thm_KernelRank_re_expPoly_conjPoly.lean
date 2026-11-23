-- Prove2me | Theorems.Thm_KernelRank_re_expPoly_conjPoly
-- name    : KernelRank.re_expPoly_conjPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:01:47.601371+00:00
-- url     : https://prove2.me/theorems/aff3c507-cf88-4968-86c2-d2fd45ffc475
-- title:
--   Kernel Rank: re exp Poly conj Poly
-- statement:
--   The Kernel Rank construction uses the re exp Poly conj Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Representation.lean#L19-L21
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Representation.lean#L19-L21

import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_Representation
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.re_expPoly_conjPoly (A : ℂ[X]) (ν : ℂ) (u : ℝ) :
    (expPoly (conjPoly A) (starRingEnd ℂ ν) u).re = (expPoly A ν u).re := by sorry
