-- Prove2me | Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_le_sub_of_nodeGapGe
-- name    : GlobalTheory.Proof.NodeGapNoncompact.le_sub_of_nodeGapGe
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:50:29.362187+00:00
-- url     : https://prove2.me/theorems/71d67e9a-e025-5029-a896-23b1f059fd80
-- title:
--   Node Gap Noncompact: le sub of node Gap Ge
-- statement:
--   The Node Gap Noncompact construction uses the le sub of node Gap Ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L91-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L91-L122

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

theorem GlobalTheory.Proof.NodeGapNoncompact.le_sub_of_nodeGapGe (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b) (hg : NodeGapGe r b h)
    (s t : Fin (2 * r + k + 1)) (hst : s < t) (hne : sign r k hk s ≠ sign r k hk t) :
    h ≤ param r k hk v b s - param r k hk v b t := by sorry
