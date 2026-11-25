-- Prove2me | Theorems.Thm_GlobalTheory_Nef_finiteDimensional_adjoin_of_trdeg_le_one
-- name    : GlobalTheory.Nef.finiteDimensional_adjoin_of_trdeg_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:50.661581+00:00
-- url     : https://prove2.me/theorems/c3bdb538-9ac4-4784-ab90-2e5accf37e42
-- title:
--   Nef: finite Dimensional adjoin of trdeg le one
-- statement:
--   The Nef construction uses the finite Dimensional adjoin of trdeg le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldOneVariableTranscendentalFiniteAndE.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldOneVariableTranscendentalFiniteAndE.lean#L11-L26

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

theorem GlobalTheory.Nef.finiteDimensional_adjoin_of_trdeg_le_one {k F : Type} [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F ≤ 1) (x : F) (hx : Transcendental k x) :
    FiniteDimensional k⟮x⟯ F := by sorry
