-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le_affine_readable
-- name    : LevyStochCalc.abs_sub_taylor_two_le_affine_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:44.71799+00:00
-- url     : https://prove2.me/theorems/5ef92fc9-92b2-4b92-8d3b-5f15ef4f7c9a
-- title:
--   Affine Second-Derivative Taylor Remainder Bound
-- statement:
--   This theorem gives a second-order Taylor estimate under an affine oscillation bound. Let E be a real normed space, f : E → ℝ, f′ and f″ the first and second Fréchet derivative fields, and A, K : ℝ with A ≥ 0 and K ≥ 0. Assume f and f′ have the stated Fréchet derivatives everywhere, and assume
--
--   $$\|f''(z)-f''(w)\|\le A+K\|z-w\|$$
--
--   for all z, w : E. Then, for all x, y : E,
--
--   $$|f(y)-f(x)-f'(x)(y-x)-\tfrac12 f''(x)(y-x)(y-x)|\le A\|y-x\|^2+K\|y-x\|^3.$$
--
--   The declaration `abs_sub_taylor_two_le_affine_readable` is useful when a uniform additive oscillation term and a Lipschitz term are available simultaneously.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_sub_taylor_two_le_affine {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
--       {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
--       (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
--       (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x y : E) :
--       |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2|
--         ≤ A * ‖y - x‖ ^ 2 + K * ‖y - x‖ ^ 3
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/TaylorTwoModulus`](https://prove2.me/theorems/9de0d95a-7af7-4d8b-902e-7044b67e5df2).
--
--   Supporting theorems: [`abs_sub_taylor_two_le_modulus_normed`](https://prove2.me/theorems/3f74f0d8-d72e-475d-8cd1-7e869d226dff).
--
--   Previous: [`abs_sub_taylor_two_le_modulus_normed`](https://prove2.me/theorems/3f74f0d8-d72e-475d-8cd1-7e869d226dff) · Next: [`abs_taylorRemainderNormed_le_affine`](https://prove2.me/theorems/be72e992-5b1b-4081-98f2-f215cb884717).
--
--   [Source excerpt, lines 142–147](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L142-L147) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L139-L164 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_sub_taylor_two_le_affine`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem LevyStochCalc.abs_sub_taylor_two_le_affine_readable {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x y : E) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2|
      ≤ A * ‖y - x‖ ^ 2 + K * ‖y - x‖ ^ 3 := by sorry
