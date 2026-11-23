-- Prove2me | Theorems.Thm_KernelRank_sum_eq_sum_upperHalf
-- name    : KernelRank.sum_eq_sum_upperHalf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:01:47.695712+00:00
-- url     : https://prove2.me/theorems/53acff6b-d221-49de-92d8-053a8c3e5f1b
-- title:
--   Kernel Rank: sum eq sum upper Half
-- statement:
--   A sum over a conjugation-closed set of rates, folded onto the closed upper half-plane.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Representation.lean#L27-L57
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Representation.lean#L27-L57

import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_Representation
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.sum_eq_sum_upperHalf (V : Finset ℂ) (hV : ∀ μ ∈ V, starRingEnd ℂ μ ∈ V) (f : ℂ → ℝ) :
    ∑ μ ∈ V, f μ = ∑ μ ∈ V.filter (fun μ => 0 ≤ μ.im),
      pairWeight μ * (f μ + f (starRingEnd ℂ μ)) := by sorry
