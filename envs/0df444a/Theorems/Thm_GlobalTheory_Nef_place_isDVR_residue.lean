-- Prove2me | Theorems.Thm_GlobalTheory_Nef_place_isDVR_residue
-- name    : GlobalTheory.Nef.place_isDVR_residue
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:15:02.045407+00:00
-- url     : https://prove2.me/theorems/da5b7ce4-0152-4c20-af36-cdedfa3e066e
-- title:
--   Nef: place is DVR residue
-- statement:
--   The Nef construction uses the place is DVR residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGround.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGround.lean#L84-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGround
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
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.place_isDVR_residue : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by sorry
