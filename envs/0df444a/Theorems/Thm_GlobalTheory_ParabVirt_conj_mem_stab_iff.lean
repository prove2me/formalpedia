-- Prove2me | Theorems.Thm_GlobalTheory_ParabVirt_conj_mem_stab_iff
-- name    : GlobalTheory.ParabVirt.conj_mem_stab_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:51.769125+00:00
-- url     : https://prove2.me/theorems/fa0555d7-ae88-43a0-aa0f-ccbf8ac7b3cc
-- title:
--   Parab Virt: conj mem stab iff
-- statement:
--   The Parab Virt construction uses the conj mem stab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean#L127-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean#L127-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.ParabVirt
variable {F : Type} [Field F] {n : ℕ}
open Polynomial
variable {F : Type} [Field F] {n : ℕ}

theorem GlobalTheory.ParabVirt.conj_mem_stab_iff (W : Submodule F (Fin n → F))
    (x t : GL (Fin n) F) :
    t⁻¹ * x * t ∈ _root_.GlobalTheory.ParabVirt.stab W ↔
      x ∈ _root_.GlobalTheory.ParabVirt.stab (W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap) := by sorry
