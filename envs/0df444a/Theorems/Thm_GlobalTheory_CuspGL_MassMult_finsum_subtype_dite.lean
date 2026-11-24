-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_MassMult_finsum_subtype_dite
-- name    : GlobalTheory.CuspGL.MassMult.finsum_subtype_dite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:31:41.205405+00:00
-- url     : https://prove2.me/theorems/86bb0f1a-7e85-4c70-99a6-0c806eac4e92
-- title:
--   Mass Mult: finsum subtype dite
-- statement:
--   The Mass Mult construction uses the finsum subtype dite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassMulParabolicInductionTrivial.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassMulParabolicInductionTrivial.lean#L14-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.MassMult
open Classical

theorem GlobalTheory.CuspGL.MassMult.finsum_subtype_dite {α : Type} [Fintype α] (p : α → Prop) (f : {x // p x} → ℂ) :
    ∑ᶠ x, f x = ∑ x, if h : p x then f ⟨x, h⟩ else 0 := by sorry
