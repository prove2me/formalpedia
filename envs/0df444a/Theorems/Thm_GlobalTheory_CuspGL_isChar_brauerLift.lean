-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_isChar_brauerLift
-- name    : GlobalTheory.CuspGL.isChar_brauerLift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:57.948577+00:00
-- url     : https://prove2.me/theorems/1176d7ee-52e7-4168-bb9b-cdb6e937f818
-- title:
--   Cusp GL: is Char brauer Lift
-- statement:
--   The Cusp GL construction uses the is Char brauer Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterBrauerLiftAbelianByPrimePower.lean#L22-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterBrauerLiftAbelianByPrimePower.lean#L22-L74

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

theorem GlobalTheory.CuspGL.isChar_brauerLift : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (G : Type) [Group G] [Finite G], AbByP G → (Nat.card G : k) ≠ 0 → ∀ (n : ℕ) (ρ : G →* GL (Fin n) k), IsChar ℂ ℂ (fun g => ((Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) k)).roots.map θ).sum) := by sorry
