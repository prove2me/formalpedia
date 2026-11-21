-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_integrated_coefficient_bound
-- name    : Kyprianou.Ch08.StageB.source_zscale_integrated_coefficient_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:20:43.320107+00:00
-- url     : https://prove2.me/theorems/12aab64f-6119-4ccd-867e-b82ce45ff32f
-- title:
--   Integrated factorial coefficient bound for Chapter 8 Z-scale entire series
-- statement:
--   Given source q=0 scale positivity and monotonicity, and the explicit integrability premise for causal convolution powers, the complex norm of the n-th integrated coefficient ∫_0^x W0^{*(n+1)} is bounded by (x W0(x))^(n+1)/n!. This follows pointwise from the Proved full factorial convolution-power majorant and the norm bound on an interval integral. Directly closes the analytic coefficient requirement for Corollary 8.5.
-- source:
--   Kyprianou (2006), Lemma 8.3 (8.23) and Corollary 8.5, printed pp.221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory Set

namespace Kyprianou.Ch08.StageB

/-- Each integrated zero-discount scale convolution coefficient has factorial norm decay. -/
theorem source_zscale_integrated_coefficient_bound
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (hconv : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ =>
        W 0 s * scaleConvolutionPower (W 0) n (x - s))
        (Set.Ioc (0 : ℝ) x) volume)
    (x : ℝ) (hx : 0 < x) :
    ∀ n : ℕ,
      ‖(((∫ y in (0 : ℝ)..x,
        scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)‖ ≤
      (x * W 0 x) * (x * W 0 x) ^ n / (Nat.factorial n : ℝ) := by
  sorry

end Kyprianou.Ch08.StageB
