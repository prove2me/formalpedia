-- Prove2me | Theorems.Thm_LevyStochCalc_abs_setIntegral_Ioc_le_readable
-- name    : LevyStochCalc.abs_setIntegral_Ioc_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:26.689397+00:00
-- url     : https://prove2.me/theorems/7eab41d0-09a0-484b-9388-f6640a71836d
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
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_setIntegral_Ioc_le {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
--       (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
--       |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/DriftIncrement`](https://prove2.me/theorems/46f140f5-271c-46b4-a62d-8c251e00fc2b).
--
--   Next: [`abs_setIntegral_Icc_sub_le`](https://prove2.me/theorems/a024dc62-1949-4b29-9d3e-69c1cee958e2).
--
--   [Source excerpt, lines 58–60](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/DriftIncrement.lean#L58-L60) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/DriftIncrement.lean#L57-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.DriftIncrement`, declaration `LevyStochCalc.abs_setIntegral_Ioc_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory

theorem LevyStochCalc.abs_setIntegral_Ioc_le_readable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a) := by sorry
