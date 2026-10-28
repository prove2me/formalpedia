-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_abs_clamp_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.abs_clamp_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:11.460712+00:00
-- url     : https://prove2.me/theorems/1920857f-1d3d-455c-88bd-4b390cbdc408
-- title:
--   Clamping Does Not Increase Distance to a Bounded Target
-- statement:
--   This elementary real-analysis lemma states that clamping a value to $[-C,C]$ cannot increase its distance from a target already in that interval.
--
--   For real numbers $C,x,y$, assume $C\ge0$ and $|y|\le C$. Then
--
--   $$
--   \left|\max(-C,\min(C,x))-y\right|\le |x-y|.
--   $$
--
--   The inequality is used to control approximation errors after applying `SimplePredictable.truncate` to coefficients.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_clamp_sub_le {C x y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C) :
--       |max (-C) (min C x) - y| ≤ |x - y|
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentLintegral`](https://prove2.me/theorems/e9dd3a38-7a56-4504-970d-056a933b183f).
--
--   Previous: [`comp_sum_ite`](https://prove2.me/theorems/d50428dd-fbc4-4845-8772-c63abee73b25) · Next: [`SimplePredictable.lintegral_pow_four_eq`](https://prove2.me/theorems/2e23b33c-826a-4615-a6b9-f62674c63f74).
--
--   [Source excerpt, lines 95–96](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean#L95-L96) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean#L94-L107 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentLintegral`, declaration `LevyStochCalc.Brownian.Ito.abs_clamp_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u

theorem LevyStochCalc.Brownian.Ito.abs_clamp_sub_le_readable {C x y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C) :
    |max (-C) (min C x) - y| ≤ |x - y| := by sorry
