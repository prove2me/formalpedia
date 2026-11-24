-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_exists_linearEquiv_mem_iff_of_finrank_eq
-- name    : GlobalTheory.CuspGL.exists_linearEquiv_mem_iff_of_finrank_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:45.964705+00:00
-- url     : https://prove2.me/theorems/b16fb76b-027f-454c-9907-4a26f2faec63
-- title:
--   Cusp GL: exists linear Equiv mem iff of finrank eq
-- statement:
--   The Cusp GL construction uses the exists linear Equiv mem iff of finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveExtendZeroOfSumUnipotentRadical.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveExtendZeroOfSumUnipotentRadical.lean#L12-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterCosetSumEqZeroOfSubgroupSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.exists_linearEquiv_mem_iff_of_finrank_eq {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A B : Submodule F V) (h : Module.finrank F A = Module.finrank F B) :
    ∃ e : V ≃ₗ[F] V, ∀ x, e x ∈ B ↔ x ∈ A := by sorry
