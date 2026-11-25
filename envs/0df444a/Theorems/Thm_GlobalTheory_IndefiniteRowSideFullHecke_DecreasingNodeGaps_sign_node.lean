-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_node
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_node
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:13:41.255802+00:00
-- url     : https://prove2.me/theorems/a38289e5-8a72-458d-86ec-22595bfa1620
-- title:
--   Decreasing Node Gaps: sign node
-- statement:
--   The Decreasing Node Gaps construction uses the sign node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DecreasingNodeGaps.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DecreasingNodeGaps.lean#L55-L58

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_node (r k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + 2)) :
    sign r k hk (nodeIdx r k hk i) = decide (Even i.val) := by sorry
