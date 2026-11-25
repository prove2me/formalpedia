-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameStabLat_map_mem_of_mem_sup_three_submodules
-- name    : GlobalTheory.HL.FrameStabLat.map_mem_of_mem_sup_three_submodules
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:31:06.462932+00:00
-- url     : https://prove2.me/theorems/0e32381d-b9bf-5753-89f5-252df55f20f3
-- title:
--   Frame Stab Lat: map mem of mem sup three submodules
-- statement:
--   The Frame Stab Lat construction uses the map mem of mem sup three submodules property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean#L78-L84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)

theorem GlobalTheory.HL.FrameStabLat.map_mem_of_mem_sup_three_submodules (A A' B Λ : Submodule O V) (h : V ≃ₗ[E] V) (H1 : ∀ x ∈ A, h x ∈ Λ)
    (H2 : ∀ x ∈ A', h x ∈ Λ) (H3 : ∀ x ∈ B, h x ∈ Λ) : ∀ x ∈ A ⊔ A' ⊔ B, h x ∈ Λ := by sorry
