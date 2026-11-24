-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_IsAlgebraicChart_analyticOnNhd_trans
-- name    : GlobalTheory.AffinePoints.IsAlgebraicChart.analyticOnNhd_trans
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:54:55.549606+00:00
-- url     : https://prove2.me/theorems/0f6fd1c4-e53e-45f2-aee8-c4b581bcfbb8
-- title:
--   Is Algebraic Chart: analytic On Nhd trans
-- statement:
--   The Is Algebraic Chart construction uses the analytic On Nhd trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L30-L46

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

theorem GlobalTheory.AffinePoints.IsAlgebraicChart.analyticOnNhd_trans
    {e e' : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜)} (he : IsAlgebraicChart e)
    (he' : IsAlgebraicChart e') : AnalyticOnNhd 𝕜 (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by sorry
