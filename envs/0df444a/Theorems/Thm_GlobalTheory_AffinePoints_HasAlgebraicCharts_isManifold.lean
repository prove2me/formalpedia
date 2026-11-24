-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_HasAlgebraicCharts_isManifold
-- name    : GlobalTheory.AffinePoints.HasAlgebraicCharts.isManifold
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:54:47.427519+00:00
-- url     : https://prove2.me/theorems/a4e56a75-c777-4b30-887f-9e1f0e3f5ef3
-- title:
--   Has Algebraic Charts: is Manifold
-- statement:
--   The Has Algebraic Charts construction uses the is Manifold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L50-L58

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

theorem GlobalTheory.AffinePoints.HasAlgebraicCharts.isManifold (h : HasAlgebraicCharts 𝕜 A d) :
    letI := h.chartedSpace
    IsManifold 𝓘(𝕜, Fin d → 𝕜) ω (A →ₐ[𝕜] 𝕜) := by sorry
