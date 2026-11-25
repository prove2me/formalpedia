-- Prove2me | Theorems.Thm_GlobalTheory_ParabVirt_mem_stab
-- name    : GlobalTheory.ParabVirt.mem_stab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:15:53.819317+00:00
-- url     : https://prove2.me/theorems/5ec7f42a-53f6-4f35-bf59-1ee41e7c4418
-- title:
--   Parab Virt: mem stab
-- statement:
--   The Parab Virt construction uses the mem stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean#L92-L94

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

theorem GlobalTheory.ParabVirt.mem_stab (W : Submodule F (Fin n → F)) (x : GL (Fin n) F) :
    x ∈ _root_.GlobalTheory.ParabVirt.stab W ↔
      ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W := by sorry
