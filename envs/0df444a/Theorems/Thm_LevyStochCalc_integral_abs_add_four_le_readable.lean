-- Prove2me | Theorems.Thm_LevyStochCalc_integral_abs_add_four_le_readable
-- name    : LevyStochCalc.integral_abs_add_four_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:47.281879+00:00
-- url     : https://prove2.me/theorems/1d271bc2-3915-4ac6-a74e-692ff5624511
-- title:
--   Four-Term Integrated Triangle Inequality
-- statement:
--   Let P be a probability measure on Ω and let a, b, c, d : Ω → ℝ be integrable with respect to P. If A, B, C, D : ℝ satisfy
--
--   $$\int|a|\,dP\le A,\quad \int|b|\,dP\le B,\quad \int|c|\,dP\le C,\quad \int|d|\,dP\le D,$$
--
--   then `integral_abs_add_four_le_readable` gives
--
--   $$\int|a+b+c+d|\,dP\le A+B+C+D.$$
--
--   This is a reusable finite-sum estimate for assembling four integrable error terms.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_add_four_le {P : Measure Ω} [IsProbabilityMeasure P]
--       {a b c d : Ω → ℝ} (ha : Integrable a P) (hb : Integrable b P) (hc : Integrable c P)
--       (hd : Integrable d P) {A B C D : ℝ} (hA : ∫ ω, |a ω| ∂P ≤ A)
--       (hB : ∫ ω, |b ω| ∂P ≤ B) (hC : ∫ ω, |c ω| ∂P ≤ C) (hD : ∫ ω, |d ω| ∂P ≤ D) :
--       ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ A + B + C + D
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/AbsMoment`](https://prove2.me/theorems/a47bc9f6-36f4-49ba-b8be-98961f4f3386).
--
--   Previous: [`integral_abs_le_sqrt_of_integral_sq_le`](https://prove2.me/theorems/bfdc1797-b9af-45f2-9493-fd8068fd1149).
--
--   [Source excerpt, lines 86–90](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/AbsMoment.lean#L86-L90) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/AbsMoment.lean#L85-L106 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.AbsMoment`, declaration `LevyStochCalc.integral_abs_add_four_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_AbsMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/AbsMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem LevyStochCalc.integral_abs_add_four_le_readable {P : Measure Ω} [IsProbabilityMeasure P]
    {a b c d : Ω → ℝ} (ha : Integrable a P) (hb : Integrable b P) (hc : Integrable c P)
    (hd : Integrable d P) {A B C D : ℝ} (hA : ∫ ω, |a ω| ∂P ≤ A)
    (hB : ∫ ω, |b ω| ∂P ≤ B) (hC : ∫ ω, |c ω| ∂P ≤ C) (hD : ∫ ω, |d ω| ∂P ≤ D) :
    ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ A + B + C + D := by sorry
