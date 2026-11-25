-- Prove2me | Theorems.Thm_GlobalTheory_HL_StrongApprox_approx
-- name    : GlobalTheory.HL.StrongApprox.approx
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:39.500036+00:00
-- url     : https://prove2.me/theorems/c46fc268-ff53-4f44-b3b6-01654456b3ee
-- title:
--   Strong Approx: approx
-- statement:
--   The Strong Approx construction uses the approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproximationAdditiveQuadraticExtension.lean#L93-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproximationAdditiveQuadraticExtension.lean#L93-L124

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
  {sig : E →ₐ[F] E}

theorem GlobalTheory.HL.StrongApprox.approx (A : Places F E sig) (z : ∀ p, (A.loc p).Fp) (hz : ∀ p, valuation (A.loc p).Fp (z p) ≤ 1)
    (h : 𝓞 F) (hh : h ≠ 0) :
    ∃ a : 𝓞 F, ∀ p, valuation (A.loc p).Fp (z p - (A.loc p).ιF (algebraMap (𝓞 F) F a)) ≤
      valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F h)) := by sorry
