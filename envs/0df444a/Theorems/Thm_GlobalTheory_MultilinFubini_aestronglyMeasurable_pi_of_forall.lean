-- Prove2me | Theorems.Thm_GlobalTheory_MultilinFubini_aestronglyMeasurable_pi_of_forall
-- name    : GlobalTheory.MultilinFubini.aestronglyMeasurable_pi_of_forall
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:03:17.730496+00:00
-- url     : https://prove2.me/theorems/efa25bbe-1cae-469d-8ec7-dbf7df99f40b
-- title:
--   Multilin Fubini: aestrongly Measurable pi of forall
-- statement:
--   The Multilin Fubini construction uses the aestrongly Measurable pi of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralContinuousMultilinearMapPiMeasure.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralContinuousMultilinearMapPiMeasure.lean#L6-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralContinuousMultilinearMapPiMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.MultilinFubini

theorem GlobalTheory.MultilinFubini.aestronglyMeasurable_pi_of_forall {α : Type*} {m0 : MeasurableSpace α} {ν : Measure α}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : ∀ i, α → E i} (hf : ∀ i, AEStronglyMeasurable (f i) ν) :
    AEStronglyMeasurable (fun x i => f i x) ν := by sorry
