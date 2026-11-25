-- Prove2me | Theorems.Thm_GlobalTheory_Nef_essFiniteType_trdeg_of_isFF
-- name    : GlobalTheory.Nef.essFiniteType_trdeg_of_isFF
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:47.05225+00:00
-- url     : https://prove2.me/theorems/b1d4c471-cb73-45df-b8c1-3b65318fe4c3
-- title:
--   Nef: ess Finite Type trdeg of is FF
-- statement:
--   The Nef construction uses the ess Finite Type trdeg of is FF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldOneVariableTranscendentalFiniteAndE.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldOneVariableTranscendentalFiniteAndE.lean#L28-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndE
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
open IntermediateField

theorem GlobalTheory.Nef.essFiniteType_trdeg_of_isFF {k F : Type} [Field k] [Field F] [Algebra k F] (h : IsFF k F) :
    Algebra.EssFiniteType k F ∧ Algebra.trdeg k F ≤ 1 := by sorry
