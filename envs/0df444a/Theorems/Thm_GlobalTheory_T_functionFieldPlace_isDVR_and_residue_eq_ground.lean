-- Prove2me | Theorems.Thm_GlobalTheory_T_functionFieldPlace_isDVR_and_residue_eq_ground
-- name    : GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:53:31.633786+00:00
-- url     : https://prove2.me/theorems/74922bea-5b7a-43cf-89ca-89e0a9a5523c
-- title:
--   T: function Field Place is DVR and residue eq ground
-- statement:
--   The T construction uses the function Field Place is DVR and residue eq ground property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGroundStatement.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGroundStatement.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGround
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGroundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by sorry
