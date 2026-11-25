-- Prove2me | Theorems.Thm_GlobalTheory_HL_LatClose_step
-- name    : GlobalTheory.HL.LatClose.step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:31.999889+00:00
-- url     : https://prove2.me/theorems/0f6bc2f2-e1bf-4d3e-86f3-5967e67bf591
-- title:
--   Lat Close: step
-- statement:
--   The Lat Close construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CloseOnCompletedLatticeOfCloseOnFrames.lean#L64-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CloseOnCompletedLatticeOfCloseOnFrames.lean#L64-L91

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFrames
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatClose
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem GlobalTheory.HL.LatClose.step (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (D : ℤ) (h : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (g : Fin m → Fin n → E) (Mx : Matrix (Fin m) (Fin m) (A.loc p).Ep) (t : (A.loc p).Fp)
    (hg : ∀ j, h (A.bc p (g j)) = ∑ i, Mx i j • A.bc p (g i))
    (hMx : ∀ i j, ∃ o ∈ (A.L p).O, (Mx - 1) i j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o)
    (hgΛ : ∀ i, (D : 𝓞 E) • g i ∈ Λ) (a : E) (ha : ∃ o : 𝓞 E, (D : E) ^ 2 * a = o) (j : Fin m) :
    ∃ z ∈ A.lat p Λ, (A.loc p).ιE a • (h (A.bc p (g j)) - A.bc p (g j)) =
      algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by sorry
