-- Prove2me | Theorems.Thm_GlobalTheory_finiteDimensional_top_subfield
-- name    : GlobalTheory.finiteDimensional_top_subfield
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:17:12.919605+00:00
-- url     : https://prove2.me/theorems/85d40aa9-4ff7-41bd-8274-9f4f741b5bac
-- title:
--   Global Theory: finite Dimensional top subfield
-- statement:
--   The Global Theory construction uses the finite Dimensional top subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormalFiniteTypeSubringInValuationSubring.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormalFiniteTypeSubringInValuationSubring.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EssFiniteTypeOfFiniteDimensionalSubfieldClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormalFiniteTypeSubringInValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.finiteDimensional_top_subfield (L : Type*) [Field L] :
    FiniteDimensional (⊤ : Subfield L) L := by sorry
