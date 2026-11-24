-- Prove2me | Theorems.Thm_GlobalTheory_AnalyticMatrixEntries_analyticAt_entry
-- name    : GlobalTheory.AnalyticMatrixEntries.analyticAt_entry
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:56:48.356393+00:00
-- url     : https://prove2.me/theorems/f22c8e99-55ba-495a-a808-2cda5845ba5d
-- title:
--   Analytic Matrix Entries: analytic At entry
-- statement:
--   The Analytic Matrix Entries construction uses the analytic At entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtEntry.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtEntry.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticMatrixEntries
universe u_1 u_2

theorem GlobalTheory.AnalyticMatrixEntries.analyticAt_entry {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {ι : Type*} (b : Module.Basis ι ℂ E) {A : X → E →L[ℂ] E} {a : X}
    (hA : AnalyticAt ℂ A a) (i j : ι) :
    AnalyticAt ℂ (fun z : X ↦ b.repr (A z (b j)) i) a := by sorry
