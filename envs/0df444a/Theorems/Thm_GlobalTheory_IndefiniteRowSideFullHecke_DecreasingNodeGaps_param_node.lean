-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_node
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:12:02.374525+00:00
-- url     : https://prove2.me/theorems/abab8cf5-2b3a-5c6e-a32b-985a47410e09
-- title:
--   Decreasing Node Gaps: param node
-- statement:
--   The Decreasing Node Gaps construction uses the param node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DecreasingNodeGaps.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DecreasingNodeGaps.lean#L44-L48

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (i : Fin (2 * r + 2)) :
    param r k hk v b (nodeIdx r k hk i) = -b i := by sorry
