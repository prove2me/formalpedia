-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_apply_fderiv_two_eq_readable
-- name    : LevyStochCalc.Brownian.Ito.sum_apply_fderiv_two_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:14.405408+00:00
-- url     : https://prove2.me/theorems/e68e16a1-d8ff-49b3-9798-30a9e8ff8724
-- title:
--   Coordinate Decomposition of the Second-Order Taylor Sum
-- statement:
--   This is the coordinate expansion of a second-order Taylor sum.
--
--   Let $n,m\in\mathbb N$, let $Y_i\in\operatorname{Fin}(n)\to\mathbb R$ be a sequence, and let $f''$ assign to each state a continuous bilinear map. Then
--   $$
--   \sum_{i<m}\frac{f''(Y_i)(Y_{i+1}-Y_i)(Y_{i+1}-Y_i)}{2}
--   =\frac12\sum_{p<n}\sum_{q<n}\sum_{i<m}
--   \partial_{pq}f''(Y_i)
--   \bigl(Y_{i+1,p}-Y_{i,p}\bigr)\bigl(Y_{i+1,q}-Y_{i,q}\bigr).
--   $$
--
--   This is an algebraic coordinate identity used to express the quadratic Taylor term in the vector Itô formula.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_apply_fderiv₂_eq (f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
--       (Y : ℕ → Fin n → ℝ) (m : ℕ) :
--       ∑ i ∈ Finset.range m, f'' (Y i) (Y (i + 1) - Y i) (Y (i + 1) - Y i) / 2
--         = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range m,
--             coordDeriv₂ f'' p q (Y i) * ((Y (i + 1) p - Y i p) * (Y (i + 1) q - Y i q))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoFormulaDecomp`](https://prove2.me/theorems/8f8fed5f-bb75-4985-83e7-6765eeac8110).
--
--   Definition modules: [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d).
--
--   Previous: [`sum_range_add_sum_comm`](https://prove2.me/theorems/3691605f-5bd6-4983-af72-18ade5e5f6bc) · Next: [`sum_apply_fderiv_eq`](https://prove2.me/theorems/77c8b45b-4dd4-41fe-8c61-8f62aefbbe0d).
--
--   [Source excerpt, lines 80–84](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L80-L84) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L79-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoFormulaDecomp`, declaration `LevyStochCalc.Brownian.Ito.sum_apply_fderiv₂_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {n : ℕ}

theorem LevyStochCalc.Brownian.Ito.sum_apply_fderiv_two_eq_readable (f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (Y : ℕ → Fin n → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, f'' (Y i) (Y (i + 1) - Y i) (Y (i + 1) - Y i) / 2
      = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range m,
          coordDeriv₂ f'' p q (Y i) * ((Y (i + 1) p - Y i p) * (Y (i + 1) q - Y i q)) := by sorry
