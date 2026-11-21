-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_compact_factorial_majorant
-- name    : Kyprianou.Ch08.StageB.source_scale_compact_factorial_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:24:34.065176+00:00
-- url     : https://prove2.me/theorems/e1c31b1b-2a91-49d4-a905-3699f4047c22
-- title:
--   Uniform factorial coefficient bound for genuine source scale convolution series
-- statement:
--   For each source scale W and q,R≥0, all real coefficients q^n F_n(x) on x∈[0,R] are bounded uniformly by W0(R) (q R W0(R))^n/n!. This follows from source W0 positivity and monotonicity and the Proved source_scale_convolution_coeff_majorant pointwise factorial estimate. Its summable majorant proves local uniform convergence and continuity of the source discount series (8.24).
-- source:
--   Kyprianou (2006), Lemma 8.3 bound (8.23), p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_scale_compact_factorial_majorant
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q R : ℝ) (hq : 0 ≤ q) (hR : 0 ≤ R) :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) R →
      ‖q ^ n * scaleConvolutionPower (W 0) n x‖ ≤
      W 0 R * (q * R * W 0 R) ^ n / (Nat.factorial n : ℝ) := by
  sorry
end Kyprianou.Ch08.StageB
