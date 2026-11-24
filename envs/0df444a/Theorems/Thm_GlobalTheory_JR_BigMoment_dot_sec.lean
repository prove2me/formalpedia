-- Prove2me | Theorems.Thm_GlobalTheory_JR_BigMoment_dot_sec
-- name    : GlobalTheory.JR.BigMoment.dot_sec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:40.716747+00:00
-- url     : https://prove2.me/theorems/bf782b02-9ce6-445b-b1b7-db2efab9f0ad
-- title:
--   Big Moment: dot sec
-- statement:
--   The Big Moment construction uses the dot sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorsMatchAtOfOneLtNormFirstMoment.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorsMatchAtOfOneLtNormFirstMoment.lean#L22-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorsMatchAtOfOneLtNormFirstMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.BigMoment

theorem GlobalTheory.JR.BigMoment.dot_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv (r + 1) k) :
    (sec a).2.2.1 ⬝ᵥ (sec a).2.1 = a.2.1 0 := by sorry
