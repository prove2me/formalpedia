-- Prove2me | Theorems.Thm_LevyStochCalc_Analysis_le_mul_pow_div_factorial_of_le_mul_setIntegral
-- name    : LevyStochCalc.Analysis.le_mul_pow_div_factorial_of_le_mul_setIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:14:59.67608+00:00
-- url     : https://prove2.me/theorems/0e253ed1-8dfb-4dff-a572-3038dffc8d21
-- title:
--   le mul pow div factorial of le mul setIntegral
-- statement:
--   The source theorem `LevyStochCalc.Analysis.le_mul_pow_div_factorial_of_le_mul_setIntegral` is extracted from `LevyStochCalc.Analysis.GronwallIntegral`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A Grönwall inequality in integral form

A nonnegative function bounded by a multiple of its own running integral is identically zero:
iterating the inequality bounds it by `B·(c(t−a))ᵐ/m!` for every `m`, and that tends to zero.
-/

open MeasureTheory

namespace LevyStochCalc.Analysis

theorem _root_.LevyStochCalc.Analysis.le_mul_pow_div_factorial_of_le_mul_setIntegral {a b c B : ℝ} (hc : 0 ≤ c)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hf0 : ∀ t, 0 ≤ f t)
    (hB : ∀ t ∈ Set.Icc a b, f t ≤ B)
    (hineq : ∀ t ∈ Set.Icc a b, f t ≤ c * ∫ u in Set.Ioc a t, f u) (m : ℕ) :
    ∀ t ∈ Set.Icc a b, f t ≤ B * (c * (t - a)) ^ m / (m).factorial := by sorry
