-- Prove2me | Theorems.Thm_GlobalTheory_T_isCharacter_cuspidal_rootSum_regular
-- name    : GlobalTheory.T.isCharacter_cuspidal_rootSum_regular
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:51:43.802033+00:00
-- url     : https://prove2.me/theorems/7c547879-f6e4-423b-93e4-c7bba938c922
-- title:
--   T: is Character cuspidal root Sum regular
-- statement:
--   The T construction uses the is Character cuspidal root Sum regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegularStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegularStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterCuspidalRootSumRegular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterCuspidalRootSumRegularStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isCharacter_cuspidal_rootSum_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ d k : ℕ, 0 < d → (∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) → IsChar ℂ ℂ (fun x : GL (Fin d) F => (-1) ^ (d - 1) * psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) ∧ ipGL (psi (rootSum θ k) (Fin d → F)) (psi (rootSum θ k) (Fin d → F)) = glCard F d := by sorry
