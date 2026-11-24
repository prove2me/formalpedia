-- Prove2me | Theorems.Thm_GlobalTheory_DefectSumCompare_pow_finrank_eq_span_absNorm
-- name    : GlobalTheory.DefectSumCompare.pow_finrank_eq_span_absNorm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:35:17.127352+00:00
-- url     : https://prove2.me/theorems/63f20e93-394c-4d04-8041-2a32166192cb
-- title:
--   Defect Sum Compare: pow finrank eq span abs Norm
-- statement:
--   The Defect Sum Compare construction uses the pow finrank eq span abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L10-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L10-L48

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open GlobalTheory GlobalTheory.DefectSumCompare

theorem GlobalTheory.DefectSumCompare.pow_finrank_eq_span_absNorm {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hfix : ∀ σ : E ≃ₐ[ℚ] E, σ • I = I) :
    I ^ Module.finrank ℚ E = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} := by sorry
