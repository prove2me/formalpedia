-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_modulus_readable
-- name    : LevyStochCalc.abs_sub_taylor_two_le_modulus_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:41.064682+00:00
-- url     : https://prove2.me/theorems/9288cfbc-c843-4593-aa84-85c99c8a03f2
-- title:
--   Real Second-Order Taylor Remainder Bound
-- statement:
--   This is a second-order Taylor remainder estimate for a twice differentiable function on ℝ. Let f, f′, f″ : ℝ → ℝ and M : ℝ satisfy M ≥ 0. Assume f′ is the derivative of f everywhere and f″ is the derivative of f′ everywhere. For x, y : ℝ, assume that every w in the interval between x and y satisfies |f″(w) − f″(x)| ≤ M. Then, with `abs_sub_taylor_two_le_modulus_readable`, the Taylor remainder obeys
--
--   $$|f(y)-f(x)-f'(x)(y-x)-\tfrac12 f''(x)(y-x)^2|\le M|y-x|^2.$$
--
--   This is the one-dimensional form of the oscillation-controlled Taylor estimate and can be reused when only a bound on the second derivative’s oscillation along the relevant segment is available.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_sub_taylor_two_le_modulus {f f' f'' : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
--       (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
--       {x y : ℝ} (hM : ∀ w ∈ Set.uIcc x y, |f'' w - f'' x| ≤ M) :
--       |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ M * |y - x| ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/TaylorTwoModulus`](https://prove2.me/theorems/9de0d95a-7af7-4d8b-902e-7044b67e5df2).
--
--   Supporting theorems: [`abs_sub_taylor_one_le_modulus`](https://prove2.me/theorems/039f7378-37a4-4a18-99b1-faedf7580c7d).
--
--   Previous: [`abs_sub_taylor_one_le_modulus`](https://prove2.me/theorems/039f7378-37a4-4a18-99b1-faedf7580c7d) · Next: [`abs_sub_taylor_two_le_modulus_normed`](https://prove2.me/theorems/3f74f0d8-d72e-475d-8cd1-7e869d226dff).
--
--   [Source excerpt, lines 53–56](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L53-L56) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L52-L94 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_sub_taylor_two_le_modulus`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

theorem LevyStochCalc.abs_sub_taylor_two_le_modulus_readable {f f' f'' : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {x y : ℝ} (hM : ∀ w ∈ Set.uIcc x y, |f'' w - f'' x| ≤ M) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ M * |y - x| ^ 2 := by sorry
