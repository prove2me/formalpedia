-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_summable
-- name    : Kyprianou.Ch08.StageB.source_scale_discount_series_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:30:33.283785+00:00
-- url     : https://prove2.me/theorems/6950572e-0d0c-4592-ad10-e3bc2248bad3
-- title:
--   Absolute summability of Chapter 8 zero-discount convolution powers for every q≥0
-- statement:
--   Under the genuine source q-scale family, explicit local integrability of the causal convolution powers, and x,q≥0, the real series Σ_n q^n W0^{*(n+1)}(x) converges absolutely. Apply the already Proved source complex coefficient factorial norm bound and Mathlib Real.summable_pow_div_factorial with parameter q x W0(x). This is the summability component of Kyprianou Lemma 8.3 (8.23).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3 inequality (8.23), printed p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- The real source discount scale series converges for every q≥0 and x≥0. -/
theorem source_scale_discount_series_summable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (hconv : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ =>
        W 0 s * scaleConvolutionPower (W 0) n (x - s))
        (Set.Ioc (0 : ℝ) x) volume)
    (x q : ℝ) (hx : 0 ≤ x) (hq : 0 ≤ q) :
    Summable (fun n : ℕ =>
      q ^ n * scaleConvolutionPower (W 0) n x) := by
  sorry

end Kyprianou.Ch08.StageB
