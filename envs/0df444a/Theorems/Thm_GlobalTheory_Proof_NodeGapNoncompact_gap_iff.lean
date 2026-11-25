-- Prove2me | Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_gap_iff
-- name    : GlobalTheory.Proof.NodeGapNoncompact.gap_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:46.60145+00:00
-- url     : https://prove2.me/theorems/97eecec9-b89f-480f-b75c-00e98b35b83c
-- title:
--   Node Gap Noncompact: gap iff
-- statement:
--   The Node Gap Noncompact construction uses the gap iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L79-L89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.NodeGapNoncompact
open PI.BesselPeriodGGP GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem GlobalTheory.Proof.NodeGapNoncompact.gap_iff (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) :
    LowGapGe h r b ↔ NodeGapGe r b h := by sorry
