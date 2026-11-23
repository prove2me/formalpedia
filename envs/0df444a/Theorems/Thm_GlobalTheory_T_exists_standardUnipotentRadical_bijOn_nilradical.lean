-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_standardUnipotentRadical_bijOn_nilradical
-- name    : GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:54.392831+00:00
-- url     : https://prove2.me/theorems/a06e978a-eee8-4aaa-a670-1de9b5fa42cc
-- title:
--   T: exists standard Unipotent Radical bij On nilradical
-- statement:
--   The T construction uses the exists standard Unipotent Radical bij On nilradical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsStandardUnipotentRadicalBijOnNilradicalStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsStandardUnipotentRadicalBijOnNilradicalStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradicalStatement
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

theorem GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical : ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (nilRad A) := by sorry
