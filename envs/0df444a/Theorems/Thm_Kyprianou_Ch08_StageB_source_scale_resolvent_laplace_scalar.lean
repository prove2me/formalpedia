-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_resolvent_laplace_scalar
-- name    : Kyprianou.Ch08.StageB.source_scale_resolvent_laplace_scalar
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:39:10.727934+00:00
-- url     : https://prove2.me/theorems/359f2ab7-e84f-41a6-b58b-5cb3e66df8a1
-- title:
--   Source q-scale resolvent Laplace identity for W0+q(W0*Wq)
-- statement:
--   For β above both zero- and q-scale roots, the scalar Laplace transform of W0+q(W0∗Wq) equals 1/(ψβ−q), exactly the transform of the actual Wq. Derive using the two source IsQScale Laplace identities, the existing Proved positive_causal_convolution_laplace_product, strict positivity of ψβ from the source scale root bridge, and elementary rational algebra. This is the essential transform equality before Laplace uniqueness in Kyprianou (8.24).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3 (8.22)-(8.24), p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- The source Wq resolvent identity holds exactly after a Laplace transform. -/
theorem source_scale_resolvent_laplace_scalar
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hroot0 : Phi ψ 0 < β) (hrootq : Phi ψ q < β) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) * W 0 x ∂volume) +
      q * (∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-(β * x)) *
          (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ∂volume) =
      (ψ β - q)⁻¹ := by
  sorry

end Kyprianou.Ch08.StageB
