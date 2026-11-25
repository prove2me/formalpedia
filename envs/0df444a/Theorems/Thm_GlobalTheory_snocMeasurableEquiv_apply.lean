-- Prove2me | Theorems.Thm_GlobalTheory_snocMeasurableEquiv_apply
-- name    : GlobalTheory.snocMeasurableEquiv_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:13.991143+00:00
-- url     : https://prove2.me/theorems/a4d93923-e7a6-4fb9-a171-d36cf347e0a1
-- title:
--   Global Theory: snoc Measurable Equiv apply
-- statement:
--   The Global Theory construction uses the snoc Measurable Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeasurePreservingSnocMeasurableEquiv.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeasurePreservingSnocMeasurableEquiv.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeasurePreservingSnocMeasurableEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.snocMeasurableEquiv_apply (n : ℕ) (p : (Fin n → ℂ) × ℂ) :
    snocMeasurableEquiv n p = Fin.snoc (α := fun _ => ℂ) p.1 p.2 := by sorry
