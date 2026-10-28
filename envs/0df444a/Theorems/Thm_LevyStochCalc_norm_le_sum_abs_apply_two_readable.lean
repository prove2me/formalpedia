-- Prove2me | Theorems.Thm_LevyStochCalc_norm_le_sum_abs_apply_two_readable
-- name    : LevyStochCalc.norm_le_sum_abs_apply_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:28.989187+00:00
-- url     : https://prove2.me/theorems/9c1c40e0-fc30-43e7-954a-44660a6d0cf5
-- title:
--   Bilinear Operator Norm Bound by Coordinates
-- statement:
--   This bounds a continuous bilinear form by its coordinate values.
--
--   For $n\in\mathbb N$ and a continuous linear map
--   $$
--   A:(\operatorname{Fin}(n)\to\mathbb R)\to
--   \bigl((\operatorname{Fin}(n)\to\mathbb R)\to\mathbb R\bigr),
--   $$
--   one has
--   $$
--   \|A\|\le
--   \sum_{p\in\operatorname{Fin}(n)}\sum_{q\in\operatorname{Fin}(n)}
--   \left|A(e_p)(e_q)\right|,
--   $$
--   where $e_p$ and $e_q$ are standard basis vectors.
--
--   This provides a coordinate bound for second derivatives and bilinear terms.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_le_sum_abs_apply₂ (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
--       ‖A‖ ≤ ∑ p, ∑ q, |A (Pi.single p 1) (Pi.single q 1)|
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d).
--
--   Previous: [`norm_le_sum_abs_apply`](https://prove2.me/theorems/08f4df99-b546-4459-b36d-34b026059891) · Next: [`abs_coordDeriv₂_sub_le_affine`](https://prove2.me/theorems/03b14996-130d-4e19-92fe-54bf2136b9a7).
--
--   [Source excerpt, lines 163–164](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CoordDerivative.lean#L163-L164) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CoordDerivative.lean#L161-L202 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CoordDerivative`, declaration `LevyStochCalc.norm_le_sum_abs_apply₂`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {n : ℕ}

theorem LevyStochCalc.norm_le_sum_abs_apply_two_readable (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, ∑ q, |A (Pi.single p 1) (Pi.single q 1)| := by sorry
