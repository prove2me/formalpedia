-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_basis_smul_eq_smul_cancel
-- name    : GlobalTheory.CuspGL.basis_smul_eq_smul_cancel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:42.701164+00:00
-- url     : https://prove2.me/theorems/f70fe54c-c9f6-4b57-b9f2-b80276f3e0be
-- title:
--   Cusp GL: basis smul eq smul cancel
-- statement:
--   The Cusp GL construction uses the basis smul eq smul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterBrauerLiftAbelianByPrimePower.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterBrauerLiftAbelianByPrimePower.lean#L10-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisAbelianByPrimePowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_TraceLiftMonomialMatrixEqSumEigenvaluesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterBrauerLiftAbelianByPrimePower
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

theorem GlobalTheory.CuspGL.basis_smul_eq_smul_cancel {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) {x y : k} {i j : ι} (hx : x ≠ 0) (h : x • b i = y • b j) :
    i = j ∧ x = y := by sorry
