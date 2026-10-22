-- Prove2me | Theorems.Thm_J6Seg_Side_jBudget6_all
-- name    : J6Seg.Side.jBudget6_all
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:35:27.745904+00:00
-- url     : https://prove2.me/theorems/c662ca2e-ace5-4100-b289-55ba66f4eb59
-- title:
--   JBudget6 for every ValCond6 / ChunkPlan6 axis plan
-- statement:
--   **$J$-pass budget for every admissible axis plan.**
--
--   For every $P.\mathrm{Ok}$ and every axis plan $ap$ with `ValCond6` and `ChunkPlan6`, the interface `JBudget6 P ap` holds.
--
--   Source packaging: eventual envelope `axJ_ev` plus per-instance `jbudget_at`. Second half of `axBudget6_of` / `axBudget6_ap6`.
-- source:
--   xuanji round-six (Solutions.J6SegJCost6); Proved J6Seg.Side.jbudget_at; feeds axBudget6_of

import Definitions.Def_IntMul_Kappa_R6_Defs70

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace J6Seg.Side

open J6Seg J6Seg.Val J6Seg.AxCh
open IntMul.Kappa.R6

theorem jBudget6_all (P : Prm) (hP : P.Ok) (ap : AxPlan6)
    (hc : ValCond6 ap) (hc' : ChunkPlan6 ap) : JBudget6 P ap := by
  sorry

end J6Seg.Side
