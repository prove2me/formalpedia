-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_regular_iff_natDegree_and_exists_elliptic
-- name    : GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:57.202763+00:00
-- url     : https://prove2.me/theorems/5aba4750-1f5b-4428-bd45-71e69af67efc
-- title:
--   Cusp GL: regular iff nat Degree and exists elliptic
-- statement:
--   The Cusp GL construction uses the regular iff nat Degree and exists elliptic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RegularIffNatDegreeAndExistsEllipticGL.lean#L62-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RegularIffNatDegreeAndExistsEllipticGL.lean#L62-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
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

theorem GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic :
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((∀ e : ℕ, 0 < e → e < n → α ^ Nat.card F ^ e ≠ α) ↔ (minpoly F α).natDegree = n) ∧ ((minpoly F α).natDegree = n → ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α) := by sorry
