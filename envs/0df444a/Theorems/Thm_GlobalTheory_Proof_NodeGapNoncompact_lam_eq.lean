-- Prove2me | Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_lam_eq
-- name    : GlobalTheory.Proof.NodeGapNoncompact.lam_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:33.654278+00:00
-- url     : https://prove2.me/theorems/e56edba3-57f5-43ce-8947-5f70943ff010
-- title:
--   Node Gap Noncompact: lam eq
-- statement:
--   The Node Gap Noncompact construction uses the lam eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L9-L21

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

theorem GlobalTheory.Proof.NodeGapNoncompact.lam_eq (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    lam48 k r v b = param r k hk v b := by sorry
