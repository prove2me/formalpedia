-- Prove2me | Theorems.Thm_LevyStochCalc_norm_le_sum_abs_apply_readable
-- name    : LevyStochCalc.norm_le_sum_abs_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:28.938101+00:00
-- url     : https://prove2.me/theorems/08f4df99-b546-4459-b36d-34b026059891
-- title:
--   Operator Norm Bound by Coordinate Values
-- statement:
--   This bounds a continuous linear functional by its values on the standard basis.
--
--   For $n\in\mathbb N$ and a continuous linear map $A:(\operatorname{Fin}(n)\to\mathbb R)\to\mathbb R$, equipped with the supremum norm, one has
--   $$
--   \|A\|\le\sum_{p\in\operatorname{Fin}(n)}
--   \left|A(e_p)\right|,
--   $$
--   where $e_p=\operatorname{Pi.single}(p,1)$ is the $p$-th standard basis vector.
--
--   This coordinate estimate is used to control first derivatives by their partial derivatives.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_le_sum_abs_apply (A : (Fin n → ℝ) →L[ℝ] ℝ) :
--       ‖A‖ ≤ ∑ p, |A (Pi.single p 1)|
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d).
--
--   Next: [`norm_le_sum_abs_apply₂`](https://prove2.me/theorems/9c1c40e0-fc30-43e7-954a-44660a6d0cf5).
--
--   [Source excerpt, lines 144–145](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CoordDerivative.lean#L144-L145) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CoordDerivative.lean#L142-L159 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CoordDerivative`, declaration `LevyStochCalc.norm_le_sum_abs_apply`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {n : ℕ}

theorem LevyStochCalc.norm_le_sum_abs_apply_readable (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ p, |A (Pi.single p 1)| := by sorry
