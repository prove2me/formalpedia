-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_laplace_transform
-- name    : Kyprianou.Ch08.StageB.source_scale_power_laplace_transform
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T00:12:02.549148+00:00
-- url     : https://prove2.me/theorems/6cea786f-1242-4a1c-8807-85c0268fad4d
-- title:
--   Geometric Laplace transform of source-scale convolution powers
-- statement:
--   For the zero-discount q-scale W and every β>Φ(0), the Laplace integral of its (n+1)-fold causal self-convolution is (1/ψ(β))^(n+1). The source W transform, the weighted convolution-powers-integrability bridge, and the existing Proved Avram causal_convolution_powers_laplace_geometric theorem give a direct formal proof. This is the crucial identity in (8.22).
-- source:
--   Kyprianou (2006), Chapter 8, Lemma 8.3 equation (8.22), printed p. 221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Each causal scale convolution power has the geometric Laplace transform. -/
theorem source_scale_power_laplace_transform
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (β : ℝ)
    (hβ : 0 ≤ β) (hroot : Phi ψ 0 < β) :
    ∀ n : ℕ,
      (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-β * t) * scaleConvolutionPower (W 0) n t ∂volume) =
        ((ψ β)⁻¹) ^ (n + 1) := by
  sorry

end Kyprianou.Ch08.StageB
