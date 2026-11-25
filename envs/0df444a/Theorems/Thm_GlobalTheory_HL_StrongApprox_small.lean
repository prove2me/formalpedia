-- Prove2me | Theorems.Thm_GlobalTheory_HL_StrongApprox_small
-- name    : GlobalTheory.HL.StrongApprox.small
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:40:19.113821+00:00
-- url     : https://prove2.me/theorems/3a915e53-7ab5-567c-bf88-05f45708e80e
-- title:
--   Strong Approx: small
-- statement:
--   The Strong Approx construction uses the small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproximationAdditiveQuadraticExtension.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproximationAdditiveQuadraticExtension.lean#L43-L56

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem GlobalTheory.HL.StrongApprox.small (A : Places F E sig) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (w : ∀ p, (A.loc p).Fp) (hw : ∀ p ∈ S, w p ≠ 0) :
    ∃ h : 𝓞 F, h ≠ 0 ∧ ∀ p ∈ S,
      valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F h)) ≤ valuation (A.loc p).Fp (w p) := by sorry
