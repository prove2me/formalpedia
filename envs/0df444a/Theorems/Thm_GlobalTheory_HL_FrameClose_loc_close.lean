-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameClose_loc_close
-- name    : GlobalTheory.HL.FrameClose.loc_close
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:55.63481+00:00
-- url     : https://prove2.me/theorems/e78108c4-a7dc-4e4e-8946-b652f73cbb63
-- title:
--   Frame Close: loc close
-- statement:
--   The Frame Close construction uses the loc close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMatrixCloseGivesLatticeCloseIntegral.lean#L117-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameMatrixCloseGivesLatticeCloseIntegral.lean#L117-L213

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitriangularCloseToOneInverseCloseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingConjInverseAdjointCloseToOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemMaximalCompactOfIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalPairingMatrixInvMulSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFramesJointGramInvMulSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCommonDenominatorForHermitianLatticeDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntCastIsUnitCompletionAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMatrixCloseGivesLatticeCloseIntegral
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClose
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem GlobalTheory.HL.FrameClose.loc_close (L : LocE F E) (r k : ℕ) (S : Frames L r k) (c a t e : F)
    (Zi : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : S.GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hc : c ≠ 0) (ha : a ∈ 𝒪[F]) (hac : a * c ∈ 𝒪[F]) (ht : t ∈ 𝒪[F]) (he : e ∈ 𝒪[F]) (he0 : e ≠ 0)
    (hZi : Zi * Matrix.of (fun i j : Fin (r + 1) => hf L S.Hm (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j)
      (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i)) = 1)
    (hZ : ∀ i j : Fin (r + 1), algebraMap F E e * hf L S.Hm (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j)
      (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i) ∈ L.O)
    (hZi' : ∀ i j, algebraMap F E e * Zi i j ∈ L.O) (hh : h ∈ S.St)
    (hM : ∀ j : Fin (r + 1), h (algebraMap F E (c ^ (r - (j : ℕ))) • S.f j) =
      ∑ i, M i j • (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i))
    (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = algebraMap F E (t * e ^ 2 * a ^ r) * o) :
    h ∈ S.K0 ∧ ∃ M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ j : Fin (r + 1), h (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j) =
        ∑ i, M' i j • (algebraMap F E (c ^ (r - (i : ℕ))) • S.f' i)) ∧
      ∀ i j, ∃ o ∈ L.O, (M' - 1) i j = algebraMap F E (t * a ^ r) * o := by sorry
