-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_finsum_nilRad_extZero_eq_zero
-- name    : GlobalTheory.CuspGL.finsum_nilRad_extZero_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:19.290796+00:00
-- url     : https://prove2.me/theorems/646d8478-c930-431c-ba07-05888673d659
-- title:
--   Cusp GL: finsum nil Rad ext Zero eq zero
-- statement:
--   The Cusp GL construction uses the finsum nil Rad ext Zero eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveExtendZeroOfSumUnipotentRadical.lean#L33-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveExtendZeroOfSumUnipotentRadical.lean#L33-L70

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

theorem GlobalTheory.CuspGL.finsum_nilRad_extZero_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ)
    (hχ : IsChar ℂ ℂ χ) (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F))
    (hb : Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1)
      (H : Set (GL (Fin d) F)) (nilRad A))
    (h0 : ∑ᶠ u ∈ (H : Set (GL (Fin d) F)), χ u = 0)
    (g : Module.End F (Fin d → F)) (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ h ∈ nilRad A, extZero χ (g + h) = 0 := by sorry
