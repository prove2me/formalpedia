-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_two_eq_iff
-- name    : KernelRank.separableRank_radial_two_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:40:15.041179+00:00
-- url     : https://prove2.me/theorems/1f5c5579-766d-45f1-bc81-d40a620dac7a
-- title:
--   Kernel Rank: separable Rank radial two eq iff
-- statement:
--   **Exact 2-D real radial rank.** Specialization of `separableRank_radial_eq_iff` to `d = 2`,
--   where `multiTotalCost 2 cs = totalCost cs`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L83-L87
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L83-L87

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.separableRank_radial_two_eq_iff (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ j, x j ^ 2)) = N ↔
      ∃ cs : List Component, IsRepresentation cs ∧
        (∀ s, 0 ≤ s → φ s = profile cs s) ∧ totalCost cs = N := by sorry
