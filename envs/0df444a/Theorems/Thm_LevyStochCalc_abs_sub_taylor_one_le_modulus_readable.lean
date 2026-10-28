-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_one_le_modulus_readable
-- name    : LevyStochCalc.abs_sub_taylor_one_le_modulus_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:32.687087+00:00
-- url     : https://prove2.me/theorems/039f7378-37a4-4a18-99b1-faedf7580c7d
-- title:
--   First-Order Taylor Remainder from Derivative Oscillation
-- statement:
--   This is a first-order Taylor remainder estimate under an oscillation bound on the derivative.
--
--   Let $f,f':\mathbb R\to\mathbb R$ and suppose that $f$ has derivative $f'(x)$ at every $x$. For $x,y\in\mathbb R$, assume that there is $M\in\mathbb R$ such that
--   $$
--   |f'(w)-f'(x)|\le M
--   $$
--   for every $w$ in the unordered interval $\operatorname{uIcc}(x,y)$. Then
--   $$
--   |f(y)-f(x)-f'(x)(y-x)|\le M|y-x|.
--   $$
--
--   This bound controls the first-order Taylor error using only the oscillation of the derivative along the segment between the two points.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_sub_taylor_one_le_modulus {f f' : ℝ → ℝ} {M : ℝ}
--       (hf : ∀ x, HasDerivAt f (f' x) x) {x y : ℝ}
--       (hM : ∀ w ∈ Set.uIcc x y, |f' w - f' x| ≤ M) :
--       |f y - f x - f' x * (y - x)| ≤ M * |y - x|
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/TaylorTwoModulus`](https://prove2.me/theorems/9de0d95a-7af7-4d8b-902e-7044b67e5df2).
--
--   Next: [`abs_sub_taylor_two_le_modulus`](https://prove2.me/theorems/9288cfbc-c843-4593-aa84-85c99c8a03f2).
--
--   [Source excerpt, lines 29–32](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L29-L32) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L28-L50 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_sub_taylor_one_le_modulus`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

theorem LevyStochCalc.abs_sub_taylor_one_le_modulus_readable {f f' : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) {x y : ℝ}
    (hM : ∀ w ∈ Set.uIcc x y, |f' w - f' x| ≤ M) :
    |f y - f x - f' x * (y - x)| ≤ M * |y - x| := by sorry
