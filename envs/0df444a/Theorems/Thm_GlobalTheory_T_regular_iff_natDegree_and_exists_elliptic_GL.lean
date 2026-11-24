-- Prove2me | Theorems.Thm_GlobalTheory_T_regular_iff_natDegree_and_exists_elliptic_GL
-- name    : GlobalTheory.T.regular_iff_natDegree_and_exists_elliptic_GL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:00.299065+00:00
-- url     : https://prove2.me/theorems/dc653376-89c5-4381-bc09-bd7e8ba9f166
-- title:
--   T: regular iff nat Degree and exists elliptic GL
-- statement:
--   The T construction uses the regular iff nat Degree and exists elliptic GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RegularIffNatDegreeAndExistsEllipticGLStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RegularIffNatDegreeAndExistsEllipticGLStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGLStatement
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

theorem GlobalTheory.T.regular_iff_natDegree_and_exists_elliptic_GL : ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((∀ e : ℕ, 0 < e → e < n → α ^ Nat.card F ^ e ≠ α) ↔ (minpoly F α).natDegree = n) ∧ ((minpoly F α).natDegree = n → ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α) := by sorry
