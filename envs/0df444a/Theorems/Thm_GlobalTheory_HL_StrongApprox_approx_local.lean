-- Prove2me | Theorems.Thm_GlobalTheory_HL_StrongApprox_approx_local
-- name    : GlobalTheory.HL.StrongApprox.approx_local
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:38:00.7476+00:00
-- url     : https://prove2.me/theorems/f18df719-7585-47c4-81d3-63eaa25f1108
-- title:
--   Strong Approx: approx local
-- statement:
--   The Strong Approx construction uses the approx local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproximationAdditiveQuadraticExtension.lean#L58-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StrongApproximationAdditiveQuadraticExtension.lean#L58-L84

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

theorem GlobalTheory.HL.StrongApprox.approx_local (T : LocAt F E sig p) (z : T.Fp) (hz : valuation T.Fp z ≤ 1) (h : 𝓞 F) (hh : h ≠ 0) :
    ∃ a : 𝓞 F, valuation T.Fp (z - T.ιF (algebraMap (𝓞 F) F a)) ≤
      valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) := by sorry
