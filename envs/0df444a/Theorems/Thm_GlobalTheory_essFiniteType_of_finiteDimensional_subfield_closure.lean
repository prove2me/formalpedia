-- Prove2me | Theorems.Thm_GlobalTheory_essFiniteType_of_finiteDimensional_subfield_closure
-- name    : GlobalTheory.essFiniteType_of_finiteDimensional_subfield_closure
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:51.955495+00:00
-- url     : https://prove2.me/theorems/95c9da6b-b232-55c5-a549-cba3d1708cf2
-- title:
--   Global Theory: ess Finite Type of finite Dimensional subfield closure
-- statement:
--   The Global Theory construction uses the ess Finite Type of finite Dimensional subfield closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EssFiniteTypeOfFiniteDimensionalSubfieldClosure.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EssFiniteTypeOfFiniteDimensionalSubfieldClosure.lean#L9-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EssFiniteTypeOfFiniteDimensionalSubfieldClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix Polynomial
open scoped BigOperators

theorem GlobalTheory.essFiniteType_of_finiteDimensional_subfield_closure {o Om : Type*} [CommRing o]
    [IsDomain o] [Field Om] [Algebra o Om] [FaithfulSMul o Om] {T : Set Om} (hT : T.Finite)
    (h : FiniteDimensional (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) Om) :
    Algebra.EssFiniteType o Om := by sorry
