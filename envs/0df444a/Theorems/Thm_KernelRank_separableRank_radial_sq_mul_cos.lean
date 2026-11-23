-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_sq_mul_cos
-- name    : KernelRank.separableRank_radial_sq_mul_cos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:42:35.009615+00:00
-- url     : https://prove2.me/theorems/e00e9581-12f4-43e0-a395-ec13c7d21405
-- title:
--   Kernel Rank: separable Rank radial sq mul cos
-- statement:
--   Exact `d`-way real separable rank of `‖x‖² cos(‖x‖²)` on `ℝ^d` (`d ≥ 2`) is `3 d - 2`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L459-L479
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L459-L479

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.separableRank_radial_sq_mul_cos {d : ℕ} (hd : 2 ≤ d) :
    separableRank (fun x : Fin d → ℝ => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2)) =
      (3 * d - 2 : ℕ) := by sorry
