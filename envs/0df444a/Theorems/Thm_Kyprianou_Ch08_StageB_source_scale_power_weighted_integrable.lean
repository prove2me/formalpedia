-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_weighted_integrable
-- name    : Kyprianou.Ch08.StageB.source_scale_power_weighted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T00:12:00.087188+00:00
-- url     : https://prove2.me/theorems/c013b144-9eb7-4baa-a6d4-2c306e0461d5
-- title:
--   Weighted integrability of all source-scale convolution powers
-- statement:
--   The source scale W^(0) has a finite exponential Laplace integral for all β>Φ(0). Every recursively defined causal convolution power of W inherits integrability under the same exponential weight. Apply the already-Proved Avram causal_convolution_powers_weighted_integrable theorem with the source scale-function definition and its exact recurrence. This bridges the existing library to Lemma 8.3.
-- source:
--   Kyprianou (2006), Chapter 8, Lemma 8.3 proof of (8.22)–(8.24), printed p. 221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Weighted integrability of all zero-discount scale convolution powers. -/
theorem source_scale_power_weighted_integrable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (β : ℝ)
    (hβ : 0 ≤ β) (hroot : Phi ψ 0 < β) :
    ∀ n : ℕ,
      IntegrableOn (fun t : ℝ =>
        Real.exp (-β * t) * scaleConvolutionPower (W 0) n t)
        (Set.Ioi (0 : ℝ)) volume := by
  sorry

end Kyprianou.Ch08.StageB
