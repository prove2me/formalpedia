-- Prove2me | Theorems.Thm_Kyprianou_Ch01_riskEmbeddedNegativeTailSource
-- name    : Kyprianou.Ch01.riskEmbeddedNegativeTailSource
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:43:50.346573+00:00
-- url     : https://prove2.me/theorems/3ec11941-844e-42c5-a866-2564eedb7945
-- title:
--   Kyprianou Exercise 1.8(iii) negative embedded-walk tail by independence
-- statement:
--   For independent exponential premium waiting times and positive claims, establish the exact strict negative tail of the product-pushforward increment law, by product Fubini and conditioning on exponential waiting time.
-- source:
--   Kyprianou (2006), Exercise 1.8(iii), worked solution printed page 304

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.riskEmbeddedNegativeTailSource
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hClaims : F (Set.Iic (0 : ℝ)) = 0) :
    let Ebeta : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e)))
    let mu : Measure ℝ :=
      (Ebeta.prod F).map (fun pair : ℝ × ℝ => pair.1 - pair.2)
    ∀ z : ℝ, 0 < z →
      (mu (Set.Iio (-z))).toReal =
        (∫ e : ℝ, (F (Set.Ioi (e + z))).toReal ∂Ebeta) := by
  sorry
