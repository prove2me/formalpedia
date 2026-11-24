-- Prove2me | Theorems.Thm_GlobalTheory_surjective_of_epi_of_field_to_field
-- name    : GlobalTheory.surjective_of_epi_of_field_to_field
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:55.987156+00:00
-- url     : https://prove2.me/theorems/2d0eeb88-ce55-4008-aa2d-963997c3dbba
-- title:
--   Global Theory: surjective of epi of field to field
-- statement:
--   The Global Theory construction uses the surjective of epi of field to field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFieldMapSurjectiveOfMono.lean#L6-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFieldMapSurjectiveOfMono.lean#L6-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldMapSurjectiveOfMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open GlobalTheory

theorem GlobalTheory.surjective_of_epi_of_field_to_field {K L : Type} [Field K] [Field L]
    (φ : CommRingCat.of K ⟶ CommRingCat.of L) [Epi φ] : Function.Surjective φ.hom := by sorry
