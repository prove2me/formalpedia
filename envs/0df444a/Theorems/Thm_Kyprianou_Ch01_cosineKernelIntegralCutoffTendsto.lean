-- Prove2me | Theorems.Thm_Kyprianou_Ch01_cosineKernelIntegralCutoffTendsto
-- name    : Kyprianou.Ch01.cosineKernelIntegralCutoffTendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:07:23.607587+00:00
-- url     : https://prove2.me/theorems/be4d7db4-b802-441a-bd67-b746582bbcb6
-- title:
--   Increasing cutoff integral of the stable index-one cosine kernel converges
-- statement:
--   The positive-line cosine kernel is integrable by already-Proved stableAlphaOneCosineIntegral, hence its integrals over increasing finite cutoffs converge to its full positive-line integral.
-- source:
--   Kyprianou (2006), Chapter 1 stable α=1 integral and Dirichlet sine integral cutoff; sourced from exact positive-lower-cutoff integration by parts and cosine kernel integral, both already Proved.

import Mathlib
open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.cosineKernelIntegralCutoffTendsto :
    Tendsto
      (fun R : ℝ =>
        ∫ x in Set.Ioc (0 : ℝ) R, (1 - Real.cos x) / x ^ 2 ∂volume)
      atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2 ∂volume)) := by
  sorry
