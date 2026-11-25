-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Basic_mulS_eq
-- name    : GlobalTheory.MomOne.Basic.mulS_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:24.31192+00:00
-- url     : https://prove2.me/theorems/6338bcdf-77e5-4541-bad8-c351c391a82d
-- title:
--   Basic: mul S eq
-- statement:
--   The Basic construction uses the mul S eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L124-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L124-L130

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

theorem GlobalTheory.MomOne.Basic.mulS_eq (a : ℤ_[q]) :
    mulS a = PowerSeries.map ((algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom) (binomialSeries ℤ_[q] a) - 1 := by sorry
