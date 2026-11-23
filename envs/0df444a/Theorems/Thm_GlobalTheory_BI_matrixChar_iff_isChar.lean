-- Prove2me | Theorems.Thm_GlobalTheory_BI_matrixChar_iff_isChar
-- name    : GlobalTheory.BI.matrixChar_iff_isChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:23.118218+00:00
-- url     : https://prove2.me/theorems/6f7a7288-ee11-4765-89f3-8266897c1c34
-- title:
--   BI: matrix Char iff is Char
-- statement:
--   The BI construction uses the matrix Char iff is Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MatrixTraceIffIsCharacterOverSubfieldComplex.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MatrixTraceIffIsCharacterOverSubfieldComplex.lean#L7-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.matrixChar_iff_isChar : ∀ (G : Type) [Group G] (χ : G → ℂ),
    (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔
      IsChar ℂ ℂ χ := by sorry
