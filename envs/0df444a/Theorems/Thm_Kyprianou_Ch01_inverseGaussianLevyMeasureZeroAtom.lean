-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianLevyMeasureZeroAtom
-- name    : Kyprianou.Ch01.inverseGaussianLevyMeasureZeroAtom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:39:25.082816+00:00
-- url     : https://prove2.me/theorems/c73d10d3-babf-4648-890b-7486ebabe886
-- title:
--   Inverse Gaussian positive-jump Lévy measure assigns no mass to zero
-- statement:
--   The original density x^(-3/2)*exp(-b²x/2), restricted to x>0, assigns zero mass to the singleton zero, for each positive b. This is the exact zero-singleton Levy-measure obligation.
-- source:
--   Kyprianou (2006), Chapter 1 inverse-Gaussian Lévy measure criterion, exact child of inverseGaussianLevyMeasureSourceExact.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianLevyMeasureZeroAtom
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    Pi {(0 : ℝ)} = 0 := by
  sorry
