-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameTri_hf_smul_right
-- name    : GlobalTheory.HL.FrameTri.hf_smul_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:38:56.218272+00:00
-- url     : https://prove2.me/theorems/385f06d7-8870-467b-949f-073ca3e47798
-- title:
--   Frame Tri: hf smul right
-- statement:
--   The Frame Tri construction uses the hf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameUnipotentUnitriangular.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameUnipotentUnitriangular.lean#L26-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTri
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.FrameTri.hf_smul_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (x a : Fin n → E) :
    hf L Hm x (c • a) = L.cj c * hf L Hm x a := by sorry
