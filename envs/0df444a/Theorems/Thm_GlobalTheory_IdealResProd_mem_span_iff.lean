-- Prove2me | Theorems.Thm_GlobalTheory_IdealResProd_mem_span_iff
-- name    : GlobalTheory.IdealResProd.mem_span_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:38:37.492805+00:00
-- url     : https://prove2.me/theorems/4815742b-f8e2-4a4e-99a6-5ad77b9c0fe9
-- title:
--   Ideal Res Prod: mem span iff
-- statement:
--   The Ideal Res Prod construction uses the mem span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AbsNormEqFinprod.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AbsNormEqFinprod.lean#L81-L96

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

theorem GlobalTheory.IdealResProd.mem_span_iff (A : LocAt F E sig p) (L : LocE A.Fp A.Ep) {c : A.Fp} (hc : c ≠ 0) (x : A.Fp) :
    algebraMap A.Fp A.Ep x ∈ Submodule.span L.O {algebraMap A.Fp A.Ep c} ↔
      valuation A.Fp x ≤ valuation A.Fp c := by sorry
