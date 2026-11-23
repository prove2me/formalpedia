-- Prove2me | Theorems.Thm_KernelRank_single_complex_rank_ge
-- name    : KernelRank.single_complex_rank_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:18:58.300839+00:00
-- url     : https://prove2.me/theorems/002891aa-06d2-42ea-98e5-650e65f5a9dd
-- title:
--   Kernel Rank: single complex rank ge
-- statement:
--   A single nonzero `d`-fold complex product `Re (β ∏ j, z j)` (`d ≥ 2`) has real rank at
--   least `d`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L864-L934
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L864-L934

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.single_complex_rank_ge {d : ℕ} (hd : 2 ≤ d) :
    ∀ {β : ℂ}, β ≠ 0 → ∀ {R : ℕ} (ℓ : Fin R → Fin d → (ℂ →ₗ[ℝ] ℝ)),
      (∀ z : Fin d → ℂ, (β * ∏ j, z j).re = ∑ n, ∏ j, ℓ n j (z j)) → d ≤ R := by sorry
