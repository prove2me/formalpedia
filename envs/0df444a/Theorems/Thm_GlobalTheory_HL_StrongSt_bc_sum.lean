-- Prove2me | Theorems.Thm_GlobalTheory_HL_StrongSt_bc_sum
-- name    : GlobalTheory.HL.StrongSt.bc_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:06:23.283716+00:00
-- url     : https://prove2.me/theorems/c598a595-e368-48f1-807a-67a6c834b1f4
-- title:
--   Strong St: bc sum
-- statement:
--   The Strong St construction uses the bc sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStab.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproxStab.lean#L44-L49

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
import Theorems.Thm_GlobalTheory_HL_LatClose_bc_sum
import Theorems.Thm_GlobalTheory_HL_RatStab_bc_sum

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

theorem GlobalTheory.HL.StrongSt.bc_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ}
    (a : Fin m → E) (x : Fin m → Fin n → E) :
    A.bc p (∑ i, a i • x i) = ∑ i, (A.loc p).ιE (a i) • A.bc p (x i) := by sorry
