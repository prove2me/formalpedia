-- Prove2me | Theorems.Thm_Kyprianou_Ch01_riskPositiveTailPushforward
-- name    : Kyprianou.Ch01.riskPositiveTailPushforward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:49:01.494036+00:00
-- url     : https://prove2.me/theorems/416dd2c1-0139-40df-8b70-aa7534d408c1
-- title:
--   Exact product-pushforward positive-tail identity via Tonelli
-- statement:
--   Tonelli decomposition of the exact independent-increment product-pushforward law: for every threshold z, the ENNReal-valued probability of e-beta minus claim greater than z equals the integral with respect to F of the exponential law upper tail above z+claim. This is a pure measure equality and does not presume the exponential survival formula.
-- source:
--   Kyprianou (2006), Exercise 1.8(iii), worked solution printed p.304

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.riskPositiveTailPushforward
  (beta : ℝ) (F : Measure ℝ) [IsProbabilityMeasure F] :
  let Ebeta : Measure ℝ :=
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e)))
  let mu : Measure ℝ := (Ebeta.prod F).map
    (fun pair : ℝ × ℝ => pair.1 - pair.2)
  ∀ z : ℝ, mu (Set.Ioi z) =
    ∫⁻ u : ℝ, Ebeta (Set.Ioi (z + u)) ∂F := by sorry
