-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_mOp_mul
-- name    : GlobalTheory.JR.WeilQuad.mOp_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:16:03.617476+00:00
-- url     : https://prove2.me/theorems/d643bc48-bdd8-5f35-b3b2-110010465d39
-- title:
--   Weil Quad: m Op mul
-- statement:
--   The Weil Quad construction uses the m Op mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepresentationQuadraticFieldExists.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepresentationQuadraticFieldExists.lean#L120-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilTorusMulUnipotentCommuteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierCompSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsStableQuadraticGaussIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGaussStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralSqEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralTransformWeilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationQuadraticFieldExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.WeilQuad.mOp_mul (A : Et F E) {ω : A.K → ℂ}
    (hmul : ∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) (a b : A.Kˣ) (φ : A.L → ℂ) :
    mOp A ω (a * b) φ = mOp A ω a (mOp A ω b φ) := by sorry
