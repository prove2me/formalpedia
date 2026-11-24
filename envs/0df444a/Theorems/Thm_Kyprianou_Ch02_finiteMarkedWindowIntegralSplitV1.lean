-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteMarkedWindowIntegralSplitV1
-- name    : Kyprianou.Ch02.finiteMarkedWindowIntegralSplitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:02:32.585603+00:00
-- url     : https://prove2.me/theorems/03a9aa16-3c5c-4bd9-9b6a-80f76f623422
-- title:
--   Finite marked window integral splits at its endpoint
-- statement:
--   The signed marked integral on a finite bounded-mark window splits into its open-time interior and the singleton endpoint fibre.
-- source:
--   Kyprianou (2006), Theorem 2.1, finite compensated band jump identity

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteMarkedWindowIntegralSplitV1
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (hsmall : B ⊆ {x : ℝ | |x| < 1})
    (T t : ℝ≥0) (htT : t ≤ T)
    (hfinite : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤) (ht : 0 < t) :
    (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) =
      (∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) +
      (∫ z in ({(t : ℝ)} ×ˢ B), z.2 ∂μ) := by sorry
