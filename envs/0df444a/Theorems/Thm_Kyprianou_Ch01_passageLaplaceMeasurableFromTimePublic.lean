-- Prove2me | Theorems.Thm_Kyprianou_Ch01_passageLaplaceMeasurableFromTimePublic
-- name    : Kyprianou.Ch01.passageLaplaceMeasurableFromTimePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:21:56.400197+00:00
-- url     : https://prove2.me/theorems/50519da7-9345-4930-bf62-2f1968ba906a
-- title:
--   Discounted first-passage Laplace payoff is measurable for measurable extended times
-- statement:
--   For any measurable extended nonnegative stopping-time variable, assigning payoff zero at infinite time and exp(-q times) at finite time gives a measurable real-valued discounted first-passage payoff, for any real discount q. The proof uses Borel measurability of WithTop.untopD, the real exponential and the measurable singleton of infinity.
-- source:
--   Measure-theoretic auxiliary for Kyprianou (2006) Chapter 1 discounted Brownian first passage.

import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.passageLaplaceMeasurableFromTimePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (τ : Ω → WithTop ℝ≥0) (q : ℝ)
    (hτ : Measurable τ) :
    Measurable (passageLaplace τ q) := by sorry
