-- Prove2me | Theorems.Thm_GlobalTheory_T_separation_numerical_ineq_cuspidalGL
-- name    : GlobalTheory.T.separation_numerical_ineq_cuspidalGL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:06.550264+00:00
-- url     : https://prove2.me/theorems/eee70a1f-66f7-47f0-9dc7-1d2d77b26fbc
-- title:
--   T: separation numerical ineq cuspidal GL
-- statement:
--   The T construction uses the separation numerical ineq cuspidal GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGLStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGLStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SeparationNumericalIneqCuspidalGL
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SeparationNumericalIneqCuspidalGLStatement
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

theorem GlobalTheory.T.separation_numerical_ineq_cuspidalGL : ∀ q n : ℕ, 2 ≤ q → 0 < n → ¬ (q = 2 ∧ (n = 4 ∨ n = 6)) → (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by sorry
