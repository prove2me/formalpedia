-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_UnipNilRad_exists_unip_bijOn_nilRad
-- name    : GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:00.29284+00:00
-- url     : https://prove2.me/theorems/e0db0fb5-f76f-490b-a05b-3d89f0f0e7b8
-- title:
--   Unip Nil Rad: exists unip bij On nil Rad
-- statement:
--   The Unip Nil Rad construction uses the exists unip bij On nil Rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsStandardUnipotentRadicalBijOnNilradical.lean#L124-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsStandardUnipotentRadicalBijOnNilradical.lean#L124-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.UnipNilRad
variable {F : Type} [Field F]
open Polynomial
variable {F : Type} [Field F]

theorem GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad :
    ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (_root_.GlobalTheory.CuspGL.nilRad A) := by sorry
