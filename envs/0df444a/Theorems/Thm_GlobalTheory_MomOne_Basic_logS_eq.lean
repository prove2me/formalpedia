-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Basic_logS_eq
-- name    : GlobalTheory.MomOne.Basic.logS_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:51.870328+00:00
-- url     : https://prove2.me/theorems/7ceb39a8-fb48-53b6-a5cc-494723443ae1
-- title:
--   Basic: log S eq
-- statement:
--   The Basic construction uses the log S eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L121-L122

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

theorem GlobalTheory.MomOne.Basic.logS_eq : (logS : ℂ_[q]⟦X⟧) = PowerSeries.log ℂ_[q] := by sorry
