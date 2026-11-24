-- Prove2me | Theorems.Thm_GlobalTheory_ParabVirt_map_eq_map_iff
-- name    : GlobalTheory.ParabVirt.map_eq_map_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:40:58.930307+00:00
-- url     : https://prove2.me/theorems/8891b1ee-58de-4a5a-ace2-a44a3f0c72d2
-- title:
--   Parab Virt: map eq map iff
-- statement:
--   The Parab Virt construction uses the map eq map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean#L106-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean#L106-L123

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

theorem GlobalTheory.ParabVirt.map_eq_map_iff (W : Submodule F (Fin n → F))
    (s t : GL (Fin n) F) :
    W.map (_root_.GlobalTheory.ParabVirt.lin s).toLinearMap =
        W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap ↔
      s⁻¹ * t ∈ _root_.GlobalTheory.ParabVirt.stab W := by sorry
