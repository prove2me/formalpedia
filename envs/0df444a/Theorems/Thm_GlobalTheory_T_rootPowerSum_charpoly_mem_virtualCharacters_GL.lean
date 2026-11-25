-- Prove2me | Theorems.Thm_GlobalTheory_T_rootPowerSum_charpoly_mem_virtualCharacters_GL
-- name    : GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:35.069612+00:00
-- url     : https://prove2.me/theorems/9025c75b-1a63-4a64-9de0-2da01fccc9f9
-- title:
--   T: root Power Sum charpoly mem virtual Characters GL
-- statement:
--   The T construction uses the root Power Sum charpoly mem virtual Characters GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGLStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGLStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGL
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharpolyMemVirtualCharactersGLStatement
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

theorem GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, (fun x : GL (Fin n) F => rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F))) ∈ Virt ℂ ℂ (GL (Fin n) F) := by sorry
