-- Prove2me | Theorems.Thm_LevyStochCalc_abs_setIntegral_Ioc_le_408915f
-- name    : LevyStochCalc.abs_setIntegral_Ioc_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:41:04.981805+00:00
-- url     : https://prove2.me/theorems/2f6fca5e-a4b2-490a-a660-fd69f996857d
-- title:
--   Bound on an Integral over a Half-Open Interval
-- statement:
--   This statement bounds the absolute value of a Lebesgue integral over a half-open interval.
--
--   Let f : ℝ → ℝ be measurable. Let B : ℝ satisfy |f(s)| ≤ B for every real s, and let a,b : ℝ satisfy a ≤ b. Then the integral of f over the interval (a,b] has absolute value at most B times the interval length:
--
--   $$
--   \left|\int_{(a,b]} f(s)\,d s\right| \le B\,(b-a).
--   $$
--
--   The result provides the basic increment estimate for the drift integral of a bounded measurable function and can be reused to establish Lipschitz and continuity properties of cumulative integrals.
--
--   **Formalization Note**: The set integral is `∫ s in Set.Ioc a b, f s ∂volume`, namely integration with respect to Lebesgue measure (`volume`) over the set `(a,b]`. The theorem states the bound under the explicit measurability, pointwise boundedness, and ordering hypotheses; integrability is not an additional premise.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/DriftIncrement.lean#L57-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.DriftIncrement`, declaration `LevyStochCalc.abs_setIntegral_Ioc_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open MeasureTheory

theorem LevyStochCalc.abs_setIntegral_Ioc_le_408915f {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a) := by sorry
