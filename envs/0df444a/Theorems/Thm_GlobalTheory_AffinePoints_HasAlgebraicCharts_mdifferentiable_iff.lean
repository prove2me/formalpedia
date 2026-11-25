-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_HasAlgebraicCharts_mdifferentiable_iff
-- name    : GlobalTheory.AffinePoints.HasAlgebraicCharts.mdifferentiable_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:54.756536+00:00
-- url     : https://prove2.me/theorems/74082c0e-5db8-5e2d-a7b5-5e54703e6f5d
-- title:
--   Has Algebraic Charts: mdifferentiable iff
-- statement:
--   The Has Algebraic Charts construction uses the mdifferentiable iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L103-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L103-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
variable [CompleteSpace 𝕜]
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]

theorem GlobalTheory.AffinePoints.HasAlgebraicCharts.mdifferentiable_iff (h : HasAlgebraicCharts 𝕜 A d)
    {φ : M → (A →ₐ[𝕜] 𝕜)} :
    letI := h.chartedSpace
    MDifferentiable I 𝓘(𝕜, Fin d → 𝕜) φ ↔ ∀ a, MDifferentiable I 𝓘(𝕜) fun m => φ m a := by sorry
