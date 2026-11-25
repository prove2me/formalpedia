-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:11:54.647178+00:00
-- url     : https://prove2.me/theorems/0d01f681-ecd5-5591-8377-f786223bf5b3
-- title:
--   Decreasing Node Gaps: param cloud
-- statement:
--   The Decreasing Node Gaps construction uses the param cloud property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DecreasingNodeGaps.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DecreasingNodeGaps.lean#L39-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (j : Fin (k - 1)) : param r k hk v b (cloudIdx r k j) = v j := by sorry
