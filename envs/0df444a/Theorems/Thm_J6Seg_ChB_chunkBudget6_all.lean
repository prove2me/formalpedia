-- Prove2me | Theorems.Thm_J6Seg_ChB_chunkBudget6_all
-- name    : J6Seg.ChB.chunkBudget6_all
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:35:31.133113+00:00
-- url     : https://prove2.me/theorems/c3c00953-21bc-4df4-9510-48dae03534de
-- title:
--   ChunkBudget6 for every ChunkPlan6 / ChunkPlanB axis plan
-- statement:
--   **Chunk-pass budget for every plan with `ChunkPlan6` and `ChunkPlanB`.**
--
--   For every $P.\mathrm{Ok}$ and every axis plan $ap$ carrying both chunk-plan interfaces, `ChunkBudget6 P ap` holds.
--
--   Third half of `axBudget6_of`, used at `ap6` once `ChunkPlanB ap6` is discharged by `decide`.
-- source:
--   xuanji round-six (Solutions.J6SegAxBud / chunk budget); feeds axBudget6_of / axBudget6_ap6

import Definitions.Def_IntMul_Kappa_R6_Defs70

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace J6Seg.ChB

open J6Seg J6Seg.AxCh
open IntMul.Kappa.R6

theorem chunkBudget6_all (P : Prm) (hP : P.Ok) (ap : AxPlan6)
    (hc : ChunkPlan6 ap) (hcb : ChunkPlanB ap) : ChunkBudget6 P ap := by
  sorry

end J6Seg.ChB
