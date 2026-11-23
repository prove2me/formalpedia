-- Prove2me | Theorems.Thm_KernelRank_separableRank_radial_lt_top_iff_exists
-- name    : KernelRank.separableRank_radial_lt_top_iff_exists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:21:38.221787+00:00
-- url     : https://prove2.me/theorems/ebc75fdf-44f1-4dc2-925a-9f1bacf4fc99
-- title:
--   Kernel Rank: separable Rank radial lt top iff exists
-- statement:
--   **Classification (`d ≥ 2`).** A real radial kernel on `ℝ^d`, with profile continuous on
--   `[0, ∞)`, has finite `d`-way separable rank if and only if its profile is, on `[0, ∞)`, a sum of
--   components.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L47-L59
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L47-L59

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.separableRank_radial_lt_top_iff_exists {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Ici 0)) :
    separableRank (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) < ⊤ ↔
      ∃ cs : List Component, IsRepresentation cs ∧ ∀ s, 0 ≤ s → φ s = profile cs s := by sorry
