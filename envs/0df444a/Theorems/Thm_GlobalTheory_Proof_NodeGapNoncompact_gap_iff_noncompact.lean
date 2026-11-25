-- Prove2me | Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_gap_iff_noncompact
-- name    : GlobalTheory.Proof.NodeGapNoncompact.gap_iff_noncompact
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:41.436573+00:00
-- url     : https://prove2.me/theorems/c9ac8c23-82ba-483f-95c1-d3542628085c
-- title:
--   Node Gap Noncompact: gap iff noncompact
-- statement:
--   The Node Gap Noncompact construction uses the gap iff noncompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L124-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L124-L133

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

theorem GlobalTheory.Proof.NodeGapNoncompact.gap_iff_noncompact (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b) :
    LowGapGe h r b ↔ NoncompactGapGe r k hk (param r k hk v b) h := by sorry
