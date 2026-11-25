-- Prove2me | Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_typings_equiv
-- name    : GlobalTheory.Proof.NodeGapNoncompact.typings_equiv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:49:17.440014+00:00
-- url     : https://prove2.me/theorems/ba833737-65e9-573b-b5f8-8745835e6b37
-- title:
--   Node Gap Noncompact: typings equiv
-- statement:
--   The Node Gap Noncompact construction uses the typings equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L148-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NodeGapNoncompact.lean#L148-L157

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

theorem GlobalTheory.Proof.NodeGapNoncompact.typings_equiv (k r : ℕ) (hk : 1 ≤ k) :
    (∀ (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), lam48 k r v b = param r k hk v b) ∧
    eps48 k r = sign r k hk ∧
    (∀ (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
      InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u) ∧
    (∀ (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
      HalfIntegralDifference k r u v b ↔ Parity r k (param r k hk v b) u) ∧
    (∀ (h : ℝ) (b : Fin (2 * r + 2) → ℝ), LowGapGe h r b ↔ NodeGapGe r b h) := by sorry
