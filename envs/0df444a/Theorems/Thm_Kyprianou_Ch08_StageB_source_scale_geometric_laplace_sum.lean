-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_geometric_laplace_sum
-- name    : Kyprianou.Ch08.StageB.source_scale_geometric_laplace_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:35:58.649174+00:00
-- url     : https://prove2.me/theorems/ee005c2b-04de-4278-b64f-c6a1a63ed35e
-- title:
--   Exact geometric series matching the source q-scale Laplace transform
-- statement:
--   Under the actual q-scale transform and β>Φψ(q), q≥0, the geometric convolution-power Laplace sum Σ_n q^n ψβ^(-n-1) equals (ψβ−q)^(-1), the actual q-scale transform. The strict positivity q<ψβ follows from the source_scale_laplace_gap_pos lemma, and the identity is exactly the Proved AvramDividend.Classical.scale_renewal_laplace_geometric_series. This is the scalar Laplace equality underpinning Kyprianou (8.24).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3 (8.22)-(8.24), printed p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- Geometric coefficient Laplace sum equals the genuine source q-scale transform. -/
theorem source_scale_geometric_laplace_sum
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hroot : Phi ψ q < β) :
    (∑' n : ℕ, q ^ n * ((ψ β)⁻¹) ^ (n + 1)) =
      (ψ β - q)⁻¹ := by
  sorry

end Kyprianou.Ch08.StageB
