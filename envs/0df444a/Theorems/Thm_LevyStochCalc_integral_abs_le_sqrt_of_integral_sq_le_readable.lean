-- Prove2me | Theorems.Thm_LevyStochCalc_integral_abs_le_sqrt_of_integral_sq_le_readable
-- name    : LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:39.936361+00:00
-- url     : https://prove2.me/theorems/bfdc1797-b9af-45f2-9493-fd8068fd1149
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
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_le_sqrt_of_integral_sq_le {P : Measure Ω} [IsProbabilityMeasure P]
--       {f : Ω → ℝ} (hf : Integrable (fun ω => |f ω|) P)
--       (hf2 : Integrable (fun ω => f ω ^ 2) P) {V : ℝ} (hV : ∫ ω, f ω ^ 2 ∂P ≤ V) :
--       ∫ ω, |f ω| ∂P ≤ Real.sqrt V
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/AbsMoment`](https://prove2.me/theorems/a47bc9f6-36f4-49ba-b8be-98961f4f3386).
--
--   Next: [`integral_abs_add_four_le`](https://prove2.me/theorems/1d271bc2-3915-4ac6-a74e-692ff5624511).
--
--   [Source excerpt, lines 31–34](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/AbsMoment.lean#L31-L34) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/AbsMoment.lean#L30-L67 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.AbsMoment`, declaration `LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_AbsMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/AbsMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le_readable {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Integrable (fun ω => |f ω|) P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) {V : ℝ} (hV : ∫ ω, f ω ^ 2 ∂P ≤ V) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt V := by sorry
