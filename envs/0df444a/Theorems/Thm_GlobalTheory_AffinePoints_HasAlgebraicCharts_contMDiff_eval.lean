-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_HasAlgebraicCharts_contMDiff_eval
-- name    : GlobalTheory.AffinePoints.HasAlgebraicCharts.contMDiff_eval
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:38.914545+00:00
-- url     : https://prove2.me/theorems/dc640bb1-4b05-4028-a66a-8c490d26542e
-- title:
--   Has Algebraic Charts: cont MDiff eval
-- statement:
--   The Has Algebraic Charts construction uses the cont MDiff eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L60-L69

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

theorem GlobalTheory.AffinePoints.HasAlgebraicCharts.contMDiff_eval (h : HasAlgebraicCharts 𝕜 A d) (a : A) :
    letI := h.chartedSpace
    ContMDiff 𝓘(𝕜, Fin d → 𝕜) 𝓘(𝕜) ω fun p : A →ₐ[𝕜] 𝕜 => p a := by sorry
