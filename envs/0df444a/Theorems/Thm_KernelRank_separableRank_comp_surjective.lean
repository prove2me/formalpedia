-- Prove2me | Theorems.Thm_KernelRank_separableRank_comp_surjective
-- name    : KernelRank.separableRank_comp_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:52.459087+00:00
-- url     : https://prove2.me/theorems/45e26e90-1b06-479d-8316-6a9c469c96a8
-- title:
--   Kernel Rank: separable Rank comp surjective
-- statement:
--   Coordinatewise surjections preserve separable rank.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L64-L77
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L64-L77

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.separableRank_comp_surjective {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X Y : ι → Type*} (K : (∀ i, X i) → 𝕜) {g : ∀ i, Y i → X i}
    (hg : ∀ i, Function.Surjective (g i)) :
    separableRank (fun y => K fun i => g i (y i)) = separableRank K := by sorry
