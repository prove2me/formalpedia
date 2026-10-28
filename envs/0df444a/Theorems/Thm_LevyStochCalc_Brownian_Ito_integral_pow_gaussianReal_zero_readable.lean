-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_pow_gaussianReal_zero_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:30.282774+00:00
-- url     : https://prove2.me/theorems/5bcebbba-553a-4972-8595-83ab7dcceb2b
-- title:
--   Scaling of Centered Gaussian Moments
-- statement:
--   This is the scaling identity for moments of a centered real Gaussian distribution.
--
--   For variance parameter $v\in[0,\infty)$ and $m\in\mathbb N$, let $\mathcal N(0,v)$ denote `gaussianReal 0 v`. Then
--   $$
--   \int x^m\,d\mathcal N(0,v)(x)
--   = (\sqrt v)^m\int x^m\,d\mathcal N(0,1)(x).
--   $$
--
--   The identity provides the variance-scaling rule used in Brownian increment moment calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_pow_gaussianReal_zero (v : ℝ≥0) (m : ℕ) :
--       ∫ x : ℝ, x ^ m ∂(gaussianReal 0 v)
--         = Real.sqrt v ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3).
--
--   Next: [`integral_mul_increment_pow`](https://prove2.me/theorems/8fc1f6bc-eb0f-42e8-a4c1-562b4c26ab81).
--
--   [Source excerpt, lines 46–48](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean#L46-L48) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentIncrements`, declaration `LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_zero`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean, lines 45-59). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u

theorem LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_zero_readable (v : ℝ≥0) (m : ℕ) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 v)
      = Real.sqrt v ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by sorry
