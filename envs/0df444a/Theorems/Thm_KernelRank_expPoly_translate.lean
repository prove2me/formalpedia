-- Prove2me | Theorems.Thm_KernelRank_expPoly_translate
-- name    : KernelRank.expPoly_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:08:09.587247+00:00
-- url     : https://prove2.me/theorems/f9331224-06d1-43fc-a027-1584e5e4edd4
-- title:
--   Kernel Rank: exp Poly translate
-- statement:
--   Taylor expansion of a translated exponential polynomial.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L18-L29
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean#L18-L29

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.expPoly_translate {P : ℂ[X]} {m : ℕ} (hm : P.natDegree < m) (μ : ℂ) (u t : ℝ) :
    expPoly P μ (u + t) =
      ∑ k : Fin m, expPoly (X ^ (k : ℕ)) μ u * expPoly (hasseDeriv k P) μ t := by sorry
