-- Prove2me | Theorems.Thm_GlobalTheory_JR_BigMoment_norm_dot_le_one
-- name    : GlobalTheory.JR.BigMoment.norm_dot_le_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:23:32.034711+00:00
-- url     : https://prove2.me/theorems/1df12b0d-15c4-4afb-be16-0fcfcbfbc480
-- title:
--   Big Moment: norm dot le one
-- statement:
--   The Big Moment construction uses the norm dot le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorsMatchAtOfOneLtNormFirstMoment.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorsMatchAtOfOneLtNormFirstMoment.lean#L8-L14

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

theorem GlobalTheory.JR.BigMoment.norm_dot_le_one {n : ℕ} {k : Type} [NormedField k] [IsUltrametricDist k] (c b : Fin n → k)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) : ‖c ⬝ᵥ b‖ ≤ 1 := by sorry
