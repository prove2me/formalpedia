-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Basic_discr_eq
-- name    : GlobalTheory.MomOne.Basic.discr_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:47.407064+00:00
-- url     : https://prove2.me/theorems/d25908a0-5e13-568a-a681-e3dba08e8d71
-- title:
--   Basic: discr eq
-- statement:
--   The Basic construction uses the discr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L150-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L150-L176

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

theorem GlobalTheory.MomOne.Basic.discr_eq {d : ℕ} {L : PeriodPair}
    (h : _root_.GlobalTheory.MomOne.IsOK d L) :
    _root_.GlobalTheory.MomOne.discr d = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ∧
      _root_.GlobalTheory.MomOne.discr d ≠ 0 := by sorry
