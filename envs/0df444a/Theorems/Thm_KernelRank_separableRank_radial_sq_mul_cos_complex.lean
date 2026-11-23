-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_sq_mul_cos_complex
-- name    : KernelRank.separableRank_radial_sq_mul_cos_complex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:42:07.548391+00:00
-- url     : https://prove2.me/theorems/d88ab212-1f37-4888-8e47-93a6685b539f
-- title:
--   Kernel Rank: separable Rank radial sq mul cos complex
-- statement:
--   Exact `d`-way complex separable rank of `‖x‖² cos(‖x‖²)` on `ℝ^d` (`d ≥ 2`) is `2 d`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L482-L509
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L482-L509

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.separableRank_radial_sq_mul_cos_complex {d : ℕ} (hd : 2 ≤ d) :
    separableRank (fun x : Fin d → ℝ =>
      (((∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2) : ℝ) : ℂ)) = (2 * d : ℕ) := by sorry
