-- Prove2me | Theorems.Thm_GlobalTheory_IdealResProd_vE_eq_count
-- name    : GlobalTheory.IdealResProd.vE_eq_count
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:40:35.776656+00:00
-- url     : https://prove2.me/theorems/90341161-2b98-540c-b1a4-4b5861f9f79a
-- title:
--   Ideal Res Prod: v E eq count
-- statement:
--   The Ideal Res Prod construction uses the v E eq count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AbsNormEqFinprod.lean#L98-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AbsNormEqFinprod.lean#L98-L124

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsNormEqFinprod
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
open GlobalTheory GlobalTheory.IdealResProd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable {p : HeightOneSpectrum (𝓞 F)}

theorem GlobalTheory.IdealResProd.vE_eq_count (A : LocAt F E sig p) (L : LocE A.Fp A.Ep) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ)
    (I : Ideal (𝓞 F)) (hI : I ≠ 0) {c : A.Fp} (hc : c ≠ 0)
    (h : Submodule.span L.O ((fun x : 𝓞 F => A.ιE (algebraMap F E x)) '' (I : Set (𝓞 F))) =
      Submodule.span L.O {algebraMap A.Fp A.Ep c}) :
    vE L ϖ (algebraMap A.Fp A.Ep c) =
      ((Associates.mk p.asIdeal).count (Associates.mk I).factors : ℕ) := by sorry
