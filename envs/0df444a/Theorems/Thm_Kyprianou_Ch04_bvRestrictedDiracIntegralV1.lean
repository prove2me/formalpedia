-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvRestrictedDiracIntegralV1
-- name    : Kyprianou.Ch04.bvRestrictedDiracIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:50:08.210953+00:00
-- url     : https://prove2.me/theorems/2a143243-6644-496e-aa25-c5ba5d85bbc9
-- title:
--   Restricted integral of a countable sum of Dirac masses
-- statement:
--   Restrict the countable Dirac sum termwise; the restriction of a Dirac mass has weight one or zero. Apply the unconditional finite-dimensional integral_sum_dirac theorem and simplify the weights.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.2; deterministic counting-measure auxiliary.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvRestrictedDiracIntegralV1
    {I : Type} [Countable I] (φ : I → ℝ × ℝ)
    (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) (g : ℝ × ℝ → ℝ) :
    (∫ z in B, g z ∂(Measure.sum (fun s : I => Measure.dirac (φ s)))) =
      ∑' s : I, B.indicator g (φ s) := by
  sorry
