-- Prove2me | Theorems.Thm_Kyprianou_Ch03_indepRectangleIntegralFactorV1
-- name    : Kyprianou.Ch03.indepRectangleIntegralFactorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:34:45.996309+00:00
-- url     : https://prove2.me/theorems/27a9b5d6-61b7-4f60-8c67-52d0621a678c
-- title:
--   Independent rectangle integral factorisation
-- statement:
--   The integral of a g-measurable real function over a g-by-h measurable rectangle factors by independence.
-- source:
--   Exercise 3.1, conditional-expectation rectangle and monotone-class argument for leaf 6a870581-0ee4-4990-b7cb-eb140983d7c6

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.indepRectangleIntegralFactorV1
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (g h : MeasurableSpace Omega) (hg : g ≤ mΩ) (hh : h ≤ mΩ)
    (hInd : @Indep Omega g h mΩ P)
    (v : Omega → ℝ) (hv : @Measurable Omega ℝ g _ v)
    (B C : Set Omega) (hB : MeasurableSet[g] B) (hC : MeasurableSet[h] C) :
    (∫ x in B ∩ C, v x ∂P) = (∫ x in B, v x ∂P) * ∫ x in C, (1 : ℝ) ∂P := by sorry
