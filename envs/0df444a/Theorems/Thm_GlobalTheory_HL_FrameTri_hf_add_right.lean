-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameTri_hf_add_right
-- name    : GlobalTheory.HL.FrameTri.hf_add_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:27:27.454149+00:00
-- url     : https://prove2.me/theorems/85f18a60-68ce-46f4-ae88-f6d1af2fc50b
-- title:
--   Frame Tri: hf add right
-- statement:
--   The Frame Tri construction uses the hf add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameUnipotentUnitriangular.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameUnipotentUnitriangular.lean#L22-L24

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

theorem GlobalTheory.HL.FrameTri.hf_add_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by sorry
