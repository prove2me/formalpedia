-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_rel_wnw
-- name    : GlobalTheory.JR.WeilQuad.rel_wnw
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:55.799439+00:00
-- url     : https://prove2.me/theorems/7c1ab33d-b91a-52dc-bf8d-71c3aac59dd4
-- title:
--   Weil Quad: rel wnw
-- statement:
--   The Weil Quad construction uses the rel wnw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepresentationQuadraticFieldExists.lean#L163-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepresentationQuadraticFieldExists.lean#L163-L181

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

theorem GlobalTheory.JR.WeilQuad.rel_wnw (A : Et F E) {ψ : AddChar F ℂ} {x : A.Kˣ} {μ : Measure A.L} {ω : A.K → ℂ}
    (H : Hyp A ψ x μ ω) (hmul : ∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t)
    (hneg : ω ((-1 : A.Kˣ) : A.K) = 1) {G₁ : ℂ} (hG0 : G₁ ≠ 0) (u : A.Kˣ) (G : ℂ)
    (hGv : G = G₁ * ω u * ((A.absK u : ℂ))⁻¹) (φ : A.L → ℂ)
    (h8 : ∀ z, fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z = G * A.psiK ψ (-((u⁻¹ : A.Kˣ) : A.K) * x * A.NL z) *
      fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ) ((-((u⁻¹ : A.Kˣ) : A.K)) • z)) :
    G₁⁻¹ • fOp A ψ x μ (nOp A ψ x u (G₁⁻¹ • fOp A ψ x μ φ)) =
      nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) (mOp A ω (-u⁻¹) (G₁⁻¹ • fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ))) := by sorry
