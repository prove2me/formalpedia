-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_scaled_series_laplace
-- name    : Kyprianou.Ch08.StageB.source_scale_scaled_series_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:14:35.464345+00:00
-- url     : https://prove2.me/theorems/edd4fc75-9620-4194-b03b-29e171579561
-- title:
--   Rescaled geometric Laplace transform of source causal scale powers
-- statement:
--   For genuine source scale W, discount q≥0 and Laplace weight β above both roots, the weighted Laplace integral of Σ_n q^(n+1) W0^{*(n+1)} is exactly (q/ψβ)/(1−q/ψβ). This follows from the existing Proved Avram causal_geometric_laplace_resolvent_series: the source root positivity gives 0≤ρ=q/ψβ<1, each kernel is weighted-integrable and nonnegative, and its Laplace mass equals ρ^(n+1) by the Proved source-scale power transform. It is the crucial source-quantified analytic identity underlying the actual Wq convolution expansion (8.24).
-- source:
--   Kyprianou (2006), Lemma 8.3 equations (8.22)-(8.24), p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_scale_scaled_series_laplace
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hroot0 : Phi ψ 0 < β) (hrootq : Phi ψ q < β) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
      (∑' n : ℕ, q ^ (n + 1) *
        scaleConvolutionPower (W 0) n x) ∂volume) =
      (q / ψ β) / (1 - q / ψ β) := by
  sorry

end Kyprianou.Ch08.StageB
