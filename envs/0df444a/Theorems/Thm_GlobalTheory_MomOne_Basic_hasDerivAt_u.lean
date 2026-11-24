-- Prove2me | Theorems.Thm_GlobalTheory_MomOne_Basic_hasDerivAt_u
-- name    : GlobalTheory.MomOne.Basic.hasDerivAt_u
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:26:36.109405+00:00
-- url     : https://prove2.me/theorems/bc66120a-036d-4777-bc9d-3f33bdcc057e
-- title:
--   Basic: has Deriv At u
-- statement:
--   The Basic construction uses the has Deriv At u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L331-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/CmLatticeCommutatorPairingPowEqOneOfGoodLift.lean#L331-L369

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

theorem GlobalTheory.MomOne.Basic.hasDerivAt_u (M : Mdl q) (hc : M.c ≠ 0) : HasDerivAt M.u M.c 0 := by sorry
