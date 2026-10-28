-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_le_add_inv_mul_sq_readable
-- name    : LevyStochCalc.Brownian.Ito.le_add_inv_mul_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:17.198656+00:00
-- url     : https://prove2.me/theorems/55fc83fc-8bfe-43c9-9ba2-4e5fb4a6199b
-- title:
--   Extended-Real Scaled Quadratic Bound
-- statement:
--   This vendored algebraic lemma gives a scaled quadratic upper bound in the extended nonnegative reals.
--
--   Let $\varepsilon,a\in[0,\infty]$ with $\varepsilon\neq0$ and $\varepsilon\neq\infty$. Then
--
--   $$
--   a\leq \varepsilon+\varepsilon^{-1}a^2.
--   $$
--
--   The inequality is a technical estimate useful for controlling a quantity by a scale parameter and a quadratic error term.
--
--   **Formalization Note.** All quantities are `ENNReal`; $\varepsilon^{-1}$ is the `ENNReal` inverse, and the hypotheses exclude both zero and top.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem le_add_inv_mul_sq {ε : ℝ≥0∞} (h0 : ε ≠ 0) (htop : ε ≠ ⊤) (a : ℝ≥0∞) :
--       a ≤ ε + ε⁻¹ * a ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionLimit`](https://prove2.me/theorems/369f5dfc-9ec0-43f0-9778-d630d2bf30a6).
--
--   Next: [`clampMesh_mono_window`](https://prove2.me/theorems/17031eaf-0282-46a9-a32a-db61ccb38eec).
--
--   [Source excerpt, lines 47–48](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L47-L48) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L46-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionLimit`, declaration `LevyStochCalc.Brownian.Ito.le_add_inv_mul_sq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal Topology

theorem LevyStochCalc.Brownian.Ito.le_add_inv_mul_sq_readable {ε : ℝ≥0∞} (h0 : ε ≠ 0) (htop : ε ≠ ⊤) (a : ℝ≥0∞) :
    a ≤ ε + ε⁻¹ * a ^ 2 := by sorry
