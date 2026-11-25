-- Prove2me | Theorems.Thm_GlobalTheory_measurePreserving_snocMeasurableEquiv
-- name    : GlobalTheory.measurePreserving_snocMeasurableEquiv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:18.293342+00:00
-- url     : https://prove2.me/theorems/c561bf8e-cbf1-4ea9-9983-dfd0b3f79fd4
-- title:
--   Global Theory: measure Preserving snoc Measurable Equiv
-- statement:
--   The Global Theory construction uses the measure Preserving snoc Measurable Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeasurePreservingSnocMeasurableEquiv.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeasurePreservingSnocMeasurableEquiv.lean#L16-L24

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

theorem GlobalTheory.measurePreserving_snocMeasurableEquiv (n : ℕ) :
    MeasurePreserving (snocMeasurableEquiv n)
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) volume := by sorry
