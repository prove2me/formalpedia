-- Prove2me | Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_interlace_iff
-- name    : GlobalTheory.Proof.NodeGapNoncompact.interlace_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:20.556465+00:00
-- url     : https://prove2.me/theorems/6d4b7d36-8c3e-51c1-b254-8e8374c6c221
-- title:
--   Node Gap Noncompact: interlace iff
-- statement:
--   The Node Gap Noncompact construction uses the interlace iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L37-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L37-L64

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

theorem GlobalTheory.Proof.NodeGapNoncompact.interlace_iff (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u := by sorry
