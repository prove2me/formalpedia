-- Prove2me | Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_sign_eq
-- name    : GlobalTheory.Proof.NodeGapNoncompact.sign_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:33.089468+00:00
-- url     : https://prove2.me/theorems/553c27a3-bad4-440a-9c44-fb7aaccf35c8
-- title:
--   Node Gap Noncompact: sign eq
-- statement:
--   The Node Gap Noncompact construction uses the sign eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L23-L35

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

theorem GlobalTheory.Proof.NodeGapNoncompact.sign_eq (k r : ℕ) (hk : 1 ≤ k) : eps48 k r = sign r k hk := by sorry
