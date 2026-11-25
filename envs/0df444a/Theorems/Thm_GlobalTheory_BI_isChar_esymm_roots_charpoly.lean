-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_esymm_roots_charpoly
-- name    : GlobalTheory.BI.isChar_esymm_roots_charpoly
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:06:55.220155+00:00
-- url     : https://prove2.me/theorems/5be2aecb-9639-4732-bf7e-9ba1e8f6efdb
-- title:
--   BI: is Char esymm roots charpoly
-- statement:
--   The BI construction uses the is Char esymm roots charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterEsymmRootsCharpoly.lean#L70-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterEsymmRootsCharpoly.lean#L70-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
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
open GlobalTheory GlobalTheory.BI
open Polynomial

theorem GlobalTheory.BI.isChar_esymm_roots_charpoly :
    ∀ (G : Type) [Group G] (n j : ℕ) (ρ : G →* GL (Fin n) ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ
      (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) := by sorry
