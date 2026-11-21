-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_weighted_laplace
-- name    : Kyprianou.Ch08.StageB.source_real_discount_series_weighted_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:29:00.862382+00:00
-- url     : https://prove2.me/theorems/e489991a-1961-4d7e-8551-ae143e91306d
-- title:
--   Exact weighted source series Laplace transform agrees with q-scale
-- statement:
--   Under the genuine source scale family and β above both zero- and q-discount roots, the real series Σq^nFn has Laplace transform (ψβ−q)⁻¹. Derive from Proved source scaled geometric series Laplace identity using q>0, with q=0 the source W0 Laplace transform. This identifies the source series transform exactly with Wq.
-- source:
--   Kyprianou (2006) Lemma 8.3 (8.24), p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_real_discount_series_weighted_laplace
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
      (ψ θ - q)⁻¹ := by
  sorry
end Kyprianou.Ch08.StageB
