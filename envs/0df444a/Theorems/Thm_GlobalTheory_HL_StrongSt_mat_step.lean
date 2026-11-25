-- Prove2me | Theorems.Thm_GlobalTheory_HL_StrongSt_mat_step
-- name    : GlobalTheory.HL.StrongSt.mat_step
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:06:06.377281+00:00
-- url     : https://prove2.me/theorems/df1bae36-4ff6-4881-ba15-35df86654d4b
-- title:
--   Strong St: mat step
-- statement:
--   The Strong St construction uses the mat step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStab.lean#L17-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStab.lean#L17-L38

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

theorem GlobalTheory.HL.StrongSt.mat_step {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (v : Fin m → V)
    (n g' : V ≃ₗ[K] V) (s t : Matrix (Fin m) (Fin m) K) (hs : IsUnit s.det)
    (hn : ∀ j, n (v j) = ∑ i, s i j • v i) (hg : ∀ j, g' (v j) = ∑ i, t i j • v i) :
    ∀ j, (n⁻¹ * g') (v j) = ∑ i, (s⁻¹ * t) i j • v i := by sorry
