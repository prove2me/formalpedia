-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Basic_cmLatticeHermitianForm_mul_left
-- name    : GlobalTheory.MomOne.Basic.cmLatticeHermitianForm_mul_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:15.174326+00:00
-- url     : https://prove2.me/theorems/73a2e95a-6b72-4d79-8482-05b5a036e2a9
-- title:
--   Basic: cm Lattice Hermitian Form mul left
-- statement:
--   The Basic construction uses the cm Lattice Hermitian Form mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L474-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L474-L476

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

theorem GlobalTheory.MomOne.Basic.cmLatticeHermitianForm_mul_left (d : ℕ) (a z w : ℂ) :
    _root_.GlobalTheory.MomOne.h1 d (a * z) w = a * _root_.GlobalTheory.MomOne.h1 d z w := by sorry
