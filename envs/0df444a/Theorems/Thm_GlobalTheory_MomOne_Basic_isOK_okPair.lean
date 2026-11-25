-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Basic_isOK_okPair
-- name    : GlobalTheory.MomOne.Basic.isOK_okPair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:18.074257+00:00
-- url     : https://prove2.me/theorems/b8ba670c-ef0f-496d-8ec9-5d0fbb479def
-- title:
--   Basic: is OK ok Pair
-- statement:
--   The Basic construction uses the is OK ok Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L191-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L191-L199

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
open PowerSeries
open scoped ComplexConjugate
variable {q : ℕ} [Fact q.Prime]
open Filter Topology

theorem GlobalTheory.MomOne.Basic.isOK_okPair (d : ℕ) (hd : 0 < d) :
    _root_.GlobalTheory.MomOne.IsOK d (_root_.GlobalTheory.MomOne.Basic.okPair d hd) := by sorry
