-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_HasAlgebraicCharts_exists_extChartAt_eventuallyEq
-- name    : GlobalTheory.AffinePoints.HasAlgebraicCharts.exists_extChartAt_eventuallyEq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:54:44.804079+00:00
-- url     : https://prove2.me/theorems/fb809dc4-2eaf-4e3a-bf02-cb720e7d2962
-- title:
--   Has Algebraic Charts: exists ext Chart At eventually Eq
-- statement:
--   The Has Algebraic Charts construction uses the exists ext Chart At eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L88-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L88-L101

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
omit [CompleteSpace 𝕜]

theorem GlobalTheory.AffinePoints.HasAlgebraicCharts.exists_extChartAt_eventuallyEq (h : HasAlgebraicCharts 𝕜 A d)
    {φ : M → (A →ₐ[𝕜] 𝕜)} {m : M} (hφ : ContinuousAt φ m) :
    letI := h.chartedSpace
    ∃ (x : Fin d → A) (s : A), φ m s ≠ 0 ∧
      extChartAt 𝓘(𝕜, Fin d → 𝕜) (φ m) ∘ φ =ᶠ[𝓝 m] fun m' i => φ m' (x i) / φ m' s := by sorry
