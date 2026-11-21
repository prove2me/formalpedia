-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_discount_series_laplace_positive_q
-- name    : Kyprianou.Ch08.StageB.source_discount_series_laplace_positive_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:29:56.378788+00:00
-- url     : https://prove2.me/theorems/75a4be2a-c6ee-49e9-a433-138feead3b07
-- title:
--   Source series Laplace equality at strictly positive discount
-- statement:
--   For actual source W0, q>0 and β above scale roots, the Laplace integral of Σq^nFn is exactly (ψβ−q)⁻¹. The Proved scaled geometric series theorem gives the same transform after multiplying by q, so cancel q using q>0 and a geometric series identity.
-- source:
--   Kyprianou (2006) Lemma 8.3 (8.24) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_discount_series_laplace_positive_q
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 < q) (hβ : 0 ≤ β)
    (hroot0 : Phi ψ 0 < β) (hrootq : Phi ψ q < β) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
      (ψ β - q)⁻¹ := by
  sorry
end Kyprianou.Ch08.StageB
