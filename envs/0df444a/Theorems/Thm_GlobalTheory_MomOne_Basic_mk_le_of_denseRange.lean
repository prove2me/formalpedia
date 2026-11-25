-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Basic_mk_le_of_denseRange
-- name    : GlobalTheory.MomOne.Basic.mk_le_of_denseRange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:57.220469+00:00
-- url     : https://prove2.me/theorems/02297799-b011-594c-840a-d6efa49e14dd
-- title:
--   Basic: mk le of dense Range
-- statement:
--   The Basic construction uses the mk le of dense Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L203-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L203-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
open Cardinal

theorem GlobalTheory.MomOne.Basic.mk_le_of_denseRange {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by sorry
