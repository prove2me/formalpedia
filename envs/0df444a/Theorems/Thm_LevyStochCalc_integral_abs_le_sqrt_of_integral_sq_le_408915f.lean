-- Prove2me | Theorems.Thm_LevyStochCalc_integral_abs_le_sqrt_of_integral_sq_le_408915f
-- name    : LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:41:05.729193+00:00
-- url     : https://prove2.me/theorems/10b56b8a-846d-4fdc-9d0b-86da9cce92cf
-- title:
--   First Absolute Moment from a Second-Moment Bound
-- statement:
--   This is a probability-space version of the first-moment bound from a second-moment estimate.
--
--   Let $P$ be a probability measure on $\Omega$, let $f:\Omega\to\mathbb R$, and let $V\in\mathbb R$. Assume that $|f|$ and $f^2$ are integrable and that
--   $$
--   \int f^2\,dP\le V.
--   $$
--   Then
--   $$
--   \int |f|\,dP\le \sqrt{V}.
--   $$
--
--   This auxiliary inequality is reusable whenever an $L^2$ estimate is available and an $L^1$ absolute-moment estimate is required.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/AbsMoment.lean#L30-L67 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.AbsMoment`, declaration `LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le_408915f {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Integrable (fun ω => |f ω|) P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) {V : ℝ} (hV : ∫ ω, f ω ^ 2 ∂P ≤ V) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt V := by sorry
