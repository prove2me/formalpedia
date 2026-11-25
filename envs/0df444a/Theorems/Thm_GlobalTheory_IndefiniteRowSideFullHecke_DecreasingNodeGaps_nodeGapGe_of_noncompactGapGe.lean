-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_nodeGapGe_of_noncompactGapGe
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.nodeGapGe_of_noncompactGapGe
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:07.864391+00:00
-- url     : https://prove2.me/theorems/e8fcbe4e-b917-5793-a92f-ce5b4fb05cf0
-- title:
--   Decreasing Node Gaps: node Gap Ge of noncompact Gap Ge
-- statement:
--   The Decreasing Node Gaps construction uses the node Gap Ge of noncompact Gap Ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DecreasingNodeGaps.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/DecreasingNodeGaps.lean#L70-L81

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.nodeGapGe_of_noncompactGapGe (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b)
    (hg : NoncompactGapGe r k hk (param r k hk v b) h) : NodeGapGe r b h := by sorry
