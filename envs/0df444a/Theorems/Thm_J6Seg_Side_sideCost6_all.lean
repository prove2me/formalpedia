-- Prove2me | Theorems.Thm_J6Seg_Side_sideCost6_all
-- name    : J6Seg.Side.sideCost6_all
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:35:45.150587+00:00
-- url     : https://prove2.me/theorems/2fb34e85-724d-41a1-8577-414bc93917a8
-- title:
--   SideCost6 for every ValCond6 / ChunkPlan6 axis plan
-- statement:
--   **Side-cost interface for every admissible axis plan.**
--
--   For every round-six parameter record $P$ with $P.\mathrm{Ok}$ and every axis plan $ap$ satisfying `ValCond6` and `ChunkPlan6`, the side-cost interface `SideCost6 P ap` holds.
--
--   In the source this is assembled from the eventual numeric envelope `axNum_ev` and the per-instance bound `side_at` (with constant $K_c(P,ap)$). The `ValCond6`/`ChunkPlan6` hypotheses are unused at this packaging layer.
--
--   This is the first of the three halves consumed by `J6Seg.ChB.axBudget6_of`, and thence by the Open leaf `axBudget6_ap6` at plan `ap6`.
-- source:
--   xuanji round-six κ development on Prove2me (jain_round6_framework solution, Solutions.J6SegSideCost); consumes Proved J6Seg.Side.side_at and J6Seg.Side.axNum_ev; feeds J6Seg.ChB.axBudget6_of / axBudget6_ap6

import Definitions.Def_IntMul_Kappa_R6_Defs70

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace J6Seg.Side

open J6Seg J6Seg.Val J6Seg.AxCh
open IntMul.Kappa.R6

theorem sideCost6_all (P : Prm) (hP : P.Ok) (ap : AxPlan6)
    (hc : ValCond6 ap) (hc' : ChunkPlan6 ap) : SideCost6 P ap := by
  sorry

end J6Seg.Side
