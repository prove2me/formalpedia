-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_all_power_local_integrability
-- name    : Kyprianou.Ch08.StageB.source_scale_all_power_local_integrability
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T00:15:43.538072+00:00
-- url     : https://prove2.me/theorems/163509ac-91a2-431c-b85e-87f332dd3389
-- title:
--   Integrability of all actual causal scale convolution integrands
-- statement:
--   The source scale function is continuous and Laplace integrable on the positive half-line; every causal convolution power has a locally integrable integrand. Use the Proved Avram weighted-integrability recursion and the boundedness of W on compact intervals. The missing analytic prerequisite for Lemma 8.3 factorial bound (8.23).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3, (8.23), printed p. 221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Kyprianou.Ch08.StageB

/-- All convolution powers of a source scale have locally integrable integrands. -/
theorem source_scale_all_power_local_integrability
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ => W 0 s * scaleConvolutionPower (W 0) n (x - s))
        (Set.Ioc (0 : ℝ) x) volume := by
  sorry

end Kyprianou.Ch08.StageB
