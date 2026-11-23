-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_eq_iff
-- name    : KernelRank.separableRank_radial_eq_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:21:26.09295+00:00
-- url     : https://prove2.me/theorems/eca6ccfb-0490-4a96-b414-4e306d79db95
-- title:
--   Kernel Rank: separable Rank radial eq iff
-- statement:
--   **Exact `d`-D real radial rank (`d ≥ 2`).** A real radial kernel on `ℝ^d`, with profile
--   continuous on `[0, ∞)`, has `d`-way separable rank `N` if and only if its profile is, on
--   `[0, ∞)`, a sum of components with distinct rates costing `multiTotalCost d cs = N` rendering
--   terms in total (`(d - 1) * deg P + 1` per real rate and `2 * (d - 1) * deg P + d` per nonreal
--   conjugate-pair rate).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L66-L79
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L66-L79

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.separableRank_radial_eq_iff {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ multiTotalCost d cs = N := by sorry
