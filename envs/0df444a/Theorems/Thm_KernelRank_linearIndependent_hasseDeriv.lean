-- Prove2me | Theorems.Thm_KernelRank_linearIndependent_hasseDeriv
-- name    : KernelRank.linearIndependent_hasseDeriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:09:58.024794+00:00
-- url     : https://prove2.me/theorems/c5ed2cf6-8861-428d-bc92-919373b7caa6
-- title:
--   Kernel Rank: linear Independent hasse Deriv
-- statement:
--   The Hasse derivatives of a nonzero polynomial are independent: their degrees are distinct.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L32-L60
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L32-L60

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.linearIndependent_hasseDeriv {P : ℂ[X]} (hP : P ≠ 0) :
    LinearIndependent ℂ (fun k : Fin (P.natDegree + 1) => hasseDeriv k P) := by sorry
