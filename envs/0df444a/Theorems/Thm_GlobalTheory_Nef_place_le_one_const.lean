-- Prove2me | Theorems.Thm_GlobalTheory_Nef_place_le_one_const
-- name    : GlobalTheory.Nef.place_le_one_const
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:21.259547+00:00
-- url     : https://prove2.me/theorems/3da64eb5-b257-44be-b3e6-b5bb17a41122
-- title:
--   Nef: place le one const
-- statement:
--   The Nef construction uses the place le one const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGround.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGround.lean#L23-L27

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

theorem GlobalTheory.Nef.place_le_one_const {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (c : k) :
    v.1 (algebraMap k F c) ≤ 1 := by sorry
