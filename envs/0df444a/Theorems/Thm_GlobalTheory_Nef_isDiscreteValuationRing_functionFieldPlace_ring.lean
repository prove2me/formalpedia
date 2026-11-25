-- Prove2me | Theorems.Thm_GlobalTheory_Nef_isDiscreteValuationRing_functionFieldPlace_ring
-- name    : GlobalTheory.Nef.isDiscreteValuationRing_functionFieldPlace_ring
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:15:24.461917+00:00
-- url     : https://prove2.me/theorems/59147edb-5f4c-4d06-a9ef-a0b6b4058fb8
-- title:
--   Nef: is Discrete Valuation Ring function Field Place ring
-- statement:
--   The Nef construction uses the is Discrete Valuation Ring function Field Place ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGround.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGround.lean#L10-L21

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

theorem GlobalTheory.Nef.isDiscreteValuationRing_functionFieldPlace_ring {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) :
    IsDiscreteValuationRing v.O := by sorry
