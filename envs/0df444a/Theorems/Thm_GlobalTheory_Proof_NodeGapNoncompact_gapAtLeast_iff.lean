-- Prove2me | Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_gapAtLeast_iff
-- name    : GlobalTheory.Proof.NodeGapNoncompact.gapAtLeast_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:17.645309+00:00
-- url     : https://prove2.me/theorems/7dfd2f21-4a84-443a-b451-1443f3434386
-- title:
--   Node Gap Noncompact: gap At Least iff
-- statement:
--   The Node Gap Noncompact construction uses the gap At Least iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L143-L146

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

theorem GlobalTheory.Proof.NodeGapNoncompact.gapAtLeast_iff (k r : ℕ) (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) :
    Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) lam h ↔ NoncompactGapGe r k hk lam h := by sorry
