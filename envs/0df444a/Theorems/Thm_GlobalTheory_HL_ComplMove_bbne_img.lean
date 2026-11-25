-- Prove2me | Theorems.Thm_GlobalTheory_HL_ComplMove_bbne_img
-- name    : GlobalTheory.HL.ComplMove.bbne_img
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:42:06.588012+00:00
-- url     : https://prove2.me/theorems/3a52545b-da1f-44ba-bb5c-23e876ac471f
-- title:
--   Compl Move: bbne img
-- statement:
--   The Compl Move construction uses the bbne img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryComplementMovesHermitianTerms.lean#L22-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryComplementMovesHermitianTerms.lean#L22-L50

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportUnitaryMassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryComplementMovesHermitianTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ComplMove
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

theorem GlobalTheory.HL.ComplMove.bbne_img (g : V ≃ₗ[E] V) (f f' : Fin (r + 1) → V) (hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b)
    (Λ : Submodule M.L.O V) (T T' : F) :
    LocNG.BBne (H := H) (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) ↔
      LocNG.BBne (H := H) (⟨Λ, f, f', T, T'⟩ : Term V M r) := by sorry
