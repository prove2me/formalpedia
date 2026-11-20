-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianLevyExponent
-- name    : Kyprianou.Ch01.inverseGaussianLevyExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:21:01.175253+00:00
-- url     : https://prove2.me/theorems/d7051c2e-e8a2-47ca-aed4-3b5b7c1c5917
-- title:
--   Exercise 1.6(ii): inverse Gaussian Lévy density and complex exponent
-- statement:
--   Kyprianou (2006), Exercise 1.6(ii), printed p. 29: the inverse Gaussian subordinator's Lévy measure Π(dx)=(2πx³)^(−1/2)exp(−b²x/2)dx on x>0 is a valid Lévy measure, and ∫₀∞(1−e^{iθx})Π(dx)=√(b²−2iθ)−b for all real θ and b>0. This identifies the non-Gaussian jump component of the characteristic exponent independently of the first-passage density. The remaining Lévy–Khintchine drift identification is a separate obligation.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.6(ii), printed p. 29, with exponent in Exercise 1.6(i).

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianLevyExponent
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    IsLevyMeasure Pi ∧
      ∀ theta : ℝ,
        IntegrableOn
          (fun x : ℝ => (1 - Complex.exp
              (Complex.I * ((theta * x : ℝ) : ℂ))))
          (Set.Ioi (0 : ℝ)) Pi ∧
        (∫ x in Set.Ioi (0 : ℝ),
          ((1 : ℂ) -
            Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
          Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
            2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
  sorry
