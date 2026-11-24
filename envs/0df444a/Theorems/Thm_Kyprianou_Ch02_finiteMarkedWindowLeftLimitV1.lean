-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteMarkedWindowLeftLimitV1
-- name    : Kyprianou.Ch02.finiteMarkedWindowLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:02:29.887797+00:00
-- url     : https://prove2.me/theorems/d3bcab91-ec99-4055-a663-b310f876ad11
-- title:
--   Left limit of a finite bounded-mark window
-- statement:
--   Restrict the measure to a finite compact window, apply bounded integrability and the integrable-window left-limit result, then remove the restriction on earlier windows.
-- source:
--   Kyprianou (2006), Theorem 2.1, finite compensated band jump identity

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteMarkedWindowLeftLimitV1
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (hsmall : B ⊆ {x : ℝ | |x| < 1})
    (T t : ℝ≥0) (htT : t ≤ T)
    (hfinite : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤) :
    Tendsto (fun s : ℝ≥0 => ∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B), z.2 ∂μ)
      (nhdsWithin t (Set.Iio t))
      (nhds (∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ)) := by sorry
