-- Prove2me | Theorems.Thm_Kyprianou_Ch03_prod_countable_measurable_left_rectanglesV1
-- name    : Kyprianou.Ch03.prod_countable_measurable_left_rectanglesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:11:48.101908+00:00
-- url     : https://prove2.me/theorems/aeee17c9-c5bf-4267-b376-e1d5929fd7c5
-- title:
--   Product outer measure of countable rectangles with measurable left factors
-- statement:
--   For countably many rectangles with measurable left factors but arbitrary right factors, the product outer measure of their union equals the lower integral of the outer measures of the right sections. The lower bound follows by applying Fubini to a measurable hull of the whole union; the upper bound follows by replacing every right factor with a measurable hull and using countable-union preservation of outer measure under measurable hulls. This handles the tail-only independent clock without adding an unsupported measurability premise.
-- source:
--   Measure-theoretic auxiliary for Kyprianou (2006) Chapter 3 Exercise 3.6; parent 8f6cb341-363a-4934-8bb1-c48730f77e03.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.prod_countable_measurable_left_rectanglesV1
    {Omega OmegaE I : Type} [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    [Countable I] (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : I → Set Omega) (B : I → Set OmegaE)
    (hA : ∀ i, MeasurableSet (A i)) :
    (P.prod Q) (⋃ i, A i ×ˢ B i) =
      ∫⁻ omega, Q (⋃ i : {i // omega ∈ A i}, B i.1) ∂P := by sorry
