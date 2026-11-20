-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplaceWithDensity
-- name    : Kyprianou.Ch01.inverseGaussianDensityLaplaceWithDensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:59:10.946063+00:00
-- url     : https://prove2.me/theorems/b24db804-f398-4b09-8c37-0e8748f34535
-- title:
--   Exact inverse Gaussian Laplace transform transfers to its weighted positive Lebesgue density
-- statement:
--   The original inverse-Gaussian passage-time density s exp(-(s-bx)^2/(2x))/sqrt(2 pi x^3) is nonnegative for x>0. The Laplace integral under the withDensity measure equals the real-weighted Lebesgue integral on x>0, with no change to b,s,q or normalisation.
-- source:
--   Kyprianou (2006) Exercise 1.6(iii), source-exact inverse Gaussian first passage law.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Kyprianou.Ch01
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianDensityLaplaceWithDensity
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) (q : ℝ) :
    (∫ x, Real.exp (-q * x) ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-((s - b * x) ^ 2 / (2 * x))))))) =
      ∫ x in Set.Ioi (0 : ℝ),
        ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-((s - b * x) ^ 2 / (2 * x)))) • Real.exp (-q * x) ∂volume := by sorry
