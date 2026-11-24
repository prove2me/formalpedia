-- Prove2me | Theorems.Thm_GlobalTheory_JR_BigMoment_dot_act
-- name    : GlobalTheory.JR.BigMoment.dot_act
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:47.655956+00:00
-- url     : https://prove2.me/theorems/407687ec-34dc-4b45-8e44-bc09cf283af4
-- title:
--   Big Moment: dot act
-- statement:
--   The Big Moment construction uses the dot act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorsMatchAtOfOneLtNormFirstMoment.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorsMatchAtOfOneLtNormFirstMoment.lean#L16-L20

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

theorem GlobalTheory.JR.BigMoment.dot_act {n : ℕ} {k : Type} [CommRing k] (g : GL (Fin n) k) (Y : Gl n k) :
    (act g Y).2.2.1 ⬝ᵥ (act g Y).2.1 = Y.2.2.1 ⬝ᵥ Y.2.1 := by sorry
