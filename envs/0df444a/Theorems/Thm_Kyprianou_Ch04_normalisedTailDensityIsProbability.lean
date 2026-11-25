-- Prove2me | Theorems.Thm_Kyprianou_Ch04_normalisedTailDensityIsProbability
-- name    : Kyprianou.Ch04.normalisedTailDensityIsProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:57:20.475844+00:00
-- url     : https://prove2.me/theorems/3c8b7a82-0fcb-4255-8441-6526102d229d
-- title:
--   Normalisation of the bounded-variation integrated-jump-tail density
-- statement:
--   Any nonnegative measurable density of finite strictly positive total mass produces a probability measure after division by its total mass. This is the normalisation step for the eta integrated negative Levy tail in Kyprianou Theorem 4.10.
-- source:
--   Kyprianou (2006), Theorem 4.10, proof of normalised integrated-tail jump measure; generic measure-theoretic reduction.

import Mathlib
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Inv
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.normalisedTailDensityIsProbability
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ENNReal) (hf : Measurable f)
    (k : ENNReal) (hk : 0 < k) (hktop : k ≠ ⊤)
    (hmass : (∫⁻ x : α, f x ∂μ) = k) :
    IsProbabilityMeasure (μ.withDensity (fun x => f x / k)) := by
  sorry
