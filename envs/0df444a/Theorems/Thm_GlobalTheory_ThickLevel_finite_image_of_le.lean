-- Prove2me | Theorems.Thm_GlobalTheory_ThickLevel_finite_image_of_le
-- name    : GlobalTheory.ThickLevel.finite_image_of_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:47:15.852628+00:00
-- url     : https://prove2.me/theorems/70c73e58-4bdf-4e13-aab2-51008e633460
-- title:
--   Thick Level: finite image of le
-- statement:
--   The Thick Level construction uses the finite image of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalisedContentThickenedSetIndependentOfLevel.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalisedContentThickenedSetIndependentOfLevel.lean#L15-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevel
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
open GlobalTheory GlobalTheory.ThickLevel

theorem GlobalTheory.ThickLevel.finite_image_of_le {W : Type} [AddCommGroup W] (B C : AddSubgroup W) (h : C.relIndex B ≠ 0)
    (T : Set W) (hT : ((QuotientAddGroup.mk : W → W ⧸ B) '' T).Finite) :
    ((QuotientAddGroup.mk : W → W ⧸ C) '' T).Finite := by sorry
