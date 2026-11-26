-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteCoefficientCrossMomentIntegral
-- name    : Kyprianou.Ch04.finiteCoefficientCrossMomentIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:39:16.943799+00:00
-- url     : https://prove2.me/theorems/151346b2-77cd-4a53-938e-6a596055cd6b
-- title:
--   Finite weighted coefficient cross-moment integration
-- statement:
--   Integrating a finite double sum of coefficient products multiplied by deterministic weights gives the weighted double sum of the coefficient cross moments under square integrability.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; deterministic energy expectation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false
universe u v w

theorem Kyprianou.Ch04.finiteCoefficientCrossMomentIntegral
    {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} [DecidableEq ι]
    (P : Measure Ω) (s : Finset ι)
    (H : ι → Ω → ℝ) (c : ι → ι → ℝ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (H i) P)
    (h2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    (∫ ω, ∑ i ∈ s, ∑ j ∈ s, (H i ω * H j ω) * c i j ∂P) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ ω, H i ω * H j ω ∂P) * c i j := by
  sorry
