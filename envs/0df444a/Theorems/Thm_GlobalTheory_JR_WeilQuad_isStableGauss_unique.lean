-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_isStableGauss_unique
-- name    : GlobalTheory.JR.WeilQuad.isStableGauss_unique
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:31.926955+00:00
-- url     : https://prove2.me/theorems/00546390-8b0d-536c-a861-74154704c33f
-- title:
--   Weil Quad: is Stable Gauss unique
-- statement:
--   The Weil Quad construction uses the is Stable Gauss unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StableQuadraticGaussIntegralTransformWeil.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StableQuadraticGaussIntegralTransformWeil.lean#L12-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussAtUniformiserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralTransformWeil
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
open scoped Pointwise

theorem GlobalTheory.JR.WeilQuad.isStableGauss_unique {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K)
    {G G' : ℂ} (h : IsStableGauss A ψ x μ u G) (h' : IsStableGauss A ψ x μ u G') : G = G' := by sorry
