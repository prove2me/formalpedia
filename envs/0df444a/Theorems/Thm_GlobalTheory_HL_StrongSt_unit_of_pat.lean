-- Prove2me | Theorems.Thm_GlobalTheory_HL_StrongSt_unit_of_pat
-- name    : GlobalTheory.HL.StrongSt.unit_of_pat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:06:55.527109+00:00
-- url     : https://prove2.me/theorems/9d7833d9-ca8a-4d9b-b378-f233be54b1bf
-- title:
--   Strong St: unit of pat
-- statement:
--   The Strong St construction uses the unit of pat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStab.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStab.lean#L51-L60

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PatternUnitriangularStrongApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalCommonStabiliserBlockUnitriangularOnFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongSt

theorem GlobalTheory.HL.StrongSt.unit_of_pat {K : Type} [CommRing K] {m : ℕ} (P : Fin m → Fin m → Prop)
    (hP : ∀ i j, P i j → i < j) (s : Matrix (Fin m) (Fin m) K)
    (hs : ∀ i j, ¬ P i j → s i j = if i = j then 1 else 0) : IsUnit s.det := by sorry
