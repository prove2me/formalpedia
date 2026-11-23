-- Prove2me | Theorems.Thm_GlobalTheory_BI_isIrreducible_transportRep
-- name    : GlobalTheory.BI.isIrreducible_transportRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:15.673213+00:00
-- url     : https://prove2.me/theorems/475f41e7-e500-4bc1-9962-be134c29c44e
-- title:
--   BI: is Irreducible transport Rep
-- statement:
--   The BI construction uses the is Irreducible transport Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean#L45-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
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
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem GlobalTheory.BI.isIrreducible_transportRep (ρ : Representation K G V) (e : V ≃ₗ[K] W)
    (h : ρ.IsIrreducible) : (transportRep ρ e).IsIrreducible := by sorry
