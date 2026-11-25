-- Prove2me | Theorems.Thm_GlobalTheory_Nef_functionFieldPlace_exists_const_sub_lt_one
-- name    : GlobalTheory.Nef.functionFieldPlace_exists_const_sub_lt_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:44.464992+00:00
-- url     : https://prove2.me/theorems/eaeef12b-da0d-47a9-8b09-132b8a3894af
-- title:
--   Nef: function Field Place exists const sub lt one
-- statement:
--   The Nef construction uses the function Field Place exists const sub lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGround.lean#L29-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceIsDVRAndResidueEqGround.lean#L29-L82

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

theorem GlobalTheory.Nef.functionFieldPlace_exists_const_sub_lt_one {k F : Type} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (hF : IsFF k F) (v : Place k F) (x : F) (hx : v.1 x ≤ 1) :
    ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by sorry
