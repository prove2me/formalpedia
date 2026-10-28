-- Prove2me | Theorems.Thm_LevyStochCalc_abs_coordDeriv_two_sub_le_affine_readable
-- name    : LevyStochCalc.abs_coordDeriv_two_sub_le_affine_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:47.149989+00:00
-- url     : https://prove2.me/theorems/03b14996-130d-4e19-92fe-54bf2136b9a7
-- title:
--   Affine Oscillation Bound for Coordinate Second Derivatives
-- statement:
--   Let n : ℕ, let f″ assign a continuous bilinear map on Fin n → ℝ to each point, and let A, K : ℝ. Assume that for all z, w : Fin n → ℝ, ‖f″(z) − f″(w)‖ ≤ A + K‖z − w‖. Then for every coordinate pair p, q : Fin n and points x, y : Fin n → ℝ, the coordinate second derivative `coordDeriv₂ f″ p q` satisfies
--
--   $$|\operatorname{coordDeriv}_2(f'',p,q,x)-\operatorname{coordDeriv}_2(f'',p,q,y)|\le A+K\|x-y\|.$$
--
--   This technical lemma transfers an operator-norm oscillation estimate to individual coordinate entries.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_coordDeriv₂_sub_le_affine {A K : ℝ} (h : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
--       (p q : Fin n) (x y : Fin n → ℝ) :
--       |coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y| ≤ A + K * ‖x - y‖
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d).
--
--   Previous: [`norm_le_sum_abs_apply₂`](https://prove2.me/theorems/9c1c40e0-fc30-43e7-954a-44660a6d0cf5).
--
--   [Source excerpt, lines 205–207](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CoordDerivative.lean#L205-L207) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CoordDerivative.lean#L204-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CoordDerivative`, declaration `LevyStochCalc.abs_coordDeriv₂_sub_le_affine`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {n : ℕ}
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}

theorem LevyStochCalc.abs_coordDeriv_two_sub_le_affine_readable {A K : ℝ} (h : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (p q : Fin n) (x y : Fin n → ℝ) :
    |coordDeriv₂ f'' p q x - coordDeriv₂ f'' p q y| ≤ A + K * ‖x - y‖ := by sorry
