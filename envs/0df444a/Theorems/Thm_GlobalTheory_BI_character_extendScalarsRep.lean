-- Prove2me | Theorems.Thm_GlobalTheory_BI_character_extendScalarsRep
-- name    : GlobalTheory.BI.character_extendScalarsRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:11.869951+00:00
-- url     : https://prove2.me/theorems/b452b658-f270-4f70-b8a1-8a996d7c43d7
-- title:
--   BI: character extend Scalars Rep
-- statement:
--   The BI construction uses the character extend Scalars Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharacterExtendScalarsRep.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharacterExtendScalarsRep.lean#L18-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterExtendScalarsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.character_extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type}
    [Group G] {n : ℕ} (ρ : Representation K G (Fin n → K)) (g : G) :
    (extendScalarsRep K L ρ).character g = algebraMap K L (ρ.character g) := by sorry
