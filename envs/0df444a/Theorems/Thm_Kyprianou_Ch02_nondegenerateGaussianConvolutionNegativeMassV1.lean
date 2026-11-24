-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nondegenerateGaussianConvolutionNegativeMassV1
-- name    : Kyprianou.Ch02.nondegenerateGaussianConvolutionNegativeMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:14:29.769002+00:00
-- url     : https://prove2.me/theorems/d7fbe9aa-0170-41f8-a324-94f0c0b9f5b3
-- title:
--   A nondegenerate Gaussian convolution has negative mass
-- statement:
--   Any probability measure puts positive mass below some finite threshold. The nondegenerate Gaussian puts positive mass below the opposite threshold. The corresponding rectangle is contained in the negative-sum event.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.nondegenerateGaussianConvolutionNegativeMassV1
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (v : ℝ≥0) (hv : 0 < v) :
    0 < (Q ∗ gaussianReal 0 v) (Iio (0 : ℝ)) := by
  sorry
