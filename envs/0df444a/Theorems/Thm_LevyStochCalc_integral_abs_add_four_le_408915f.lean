-- Prove2me | Theorems.Thm_LevyStochCalc_integral_abs_add_four_le_408915f
-- name    : LevyStochCalc.integral_abs_add_four_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:49:33.122849+00:00
-- url     : https://prove2.me/theorems/496ec5bd-b105-4642-8202-c55549ef4c95
-- title:
--   Four-Term Integrated Triangle Inequality
-- statement:
--   Let P be a probability measure on Ω and let a, b, c, d : Ω → ℝ be integrable with respect to P. If A, B, C, D : ℝ satisfy
--
--   $$\int|a|\,dP\le A,\quad \int|b|\,dP\le B,\quad \int|c|\,dP\le C,\quad \int|d|\,dP\le D,$$
--
--   then `integral_abs_add_four_le` gives
--
--   $$\int|a+b+c+d|\,dP\le A+B+C+D.$$
--
--   This is a reusable finite-sum estimate for assembling four integrable error terms.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/AbsMoment.lean#L85-L106 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.AbsMoment`, declaration `LevyStochCalc.integral_abs_add_four_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/AbsMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem LevyStochCalc.integral_abs_add_four_le_408915f {P : Measure Ω} [IsProbabilityMeasure P]
    {a b c d : Ω → ℝ} (ha : Integrable a P) (hb : Integrable b P) (hc : Integrable c P)
    (hd : Integrable d P) {A B C D : ℝ} (hA : ∫ ω, |a ω| ∂P ≤ A)
    (hB : ∫ ω, |b ω| ∂P ≤ B) (hC : ∫ ω, |c ω| ∂P ≤ C) (hD : ∫ ω, |d ω| ∂P ≤ D) :
    ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ A + B + C + D := by sorry
