-- Prove2me | Theorems.Thm_KernelRank_multiTotalCost_eq_borderTotalCost_add
-- name    : KernelRank.multiTotalCost_eq_borderTotalCost_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:26:13.958805+00:00
-- url     : https://prove2.me/theorems/bd11901b-2471-4a63-81c0-b0273ce9fdac
-- title:
--   Kernel Rank: multi Total Cost eq border Total Cost add
-- statement:
--   Exact-minus-border rank gap identity (`d ≥ 2`): for every component list `cs`,
--   `multiTotalCost d cs = borderTotalCost d cs + (d - 2) * ∑_{c ∈ cs} deg P_c`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L206-L216
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L206-L216

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.multiTotalCost_eq_borderTotalCost_add {d : ℕ} (hd : 2 ≤ d) (cs : List Component) :
    multiTotalCost d cs =
      borderTotalCost d cs + (d - 2) * (cs.map fun c => c.poly.natDegree).sum := by sorry
