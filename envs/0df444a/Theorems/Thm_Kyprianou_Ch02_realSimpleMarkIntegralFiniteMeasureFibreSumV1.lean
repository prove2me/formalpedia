-- Prove2me | Theorems.Thm_Kyprianou_Ch02_realSimpleMarkIntegralFiniteMeasureFibreSumV1
-- name    : Kyprianou.Ch02.realSimpleMarkIntegralFiniteMeasureFibreSumV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:25:35.318602+00:00
-- url     : https://prove2.me/theorems/bd25f5d7-a0e3-4141-9f89-b68849c784cc
-- title:
--   Finite-measure real simple mark integral equals finite weighted mass of mark fibres
-- statement:
--   For a finite measure μ on real time-mark space and a real simple mark f, the signed Bochner integral of f(z.2) equals the finite sum over the actual finite range of f of x times μ{(time,mark):f(mark)=x}. Prove using SimpleFunc.comp f Prod.snd measurable_snd, SimpleFunc.integrable_of_isFiniteMeasure, SimpleFunc.integral_eq_sum, SimpleFunc.range_comp_subset_range plus surjectivity of Prod.snd, and real scalar multiplication. This is the deterministic identification required to lift the already Proved finite-vector Poisson count joint stationary laws to finite-simple marked Poisson integral laws for Kyprianou Eq. (2.3).
-- source:
--   Mathlib SimpleFunc integral_eq_sum, Kyprianou (2006) Eq. (2.3).

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.realSimpleMarkIntegralFiniteMeasureFibreSumV1
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (f : SimpleFunc ℝ ℝ) :
    (∫ z : ℝ × ℝ, f z.2 ∂μ) =
      ∑ x ∈ f.range, (μ {p : ℝ × ℝ | f p.2 = x}).toReal * x := by sorry
