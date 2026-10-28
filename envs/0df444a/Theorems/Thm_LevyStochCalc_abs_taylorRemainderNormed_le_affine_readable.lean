-- Prove2me | Theorems.Thm_LevyStochCalc_abs_taylorRemainderNormed_le_affine_readable
-- name    : LevyStochCalc.abs_taylorRemainderNormed_le_affine_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:49.551104+00:00
-- url     : https://prove2.me/theorems/be72e992-5b1b-4081-98f2-f215cb884717
-- title:
--   Telescoped Taylor Remainder Along A Sequence
-- statement:
--   This theorem bounds the accumulated second-order Taylor remainder along a finite sequence. Let E, f, f′, f″, A, and K satisfy the same normed-space differentiability and nonnegativity assumptions as in `abs_sub_taylor_two_le_affine_readable`, including ‖f″(z) − f″(w)‖ ≤ A + K‖z − w‖. For a sequence x : ℕ → E and m : ℕ, the definition `taylorRemainderNormed` satisfies
--
--   $$|\operatorname{taylorRemainderNormed}(f,f',f'',x,m)|\le A\sum_{i<m}\|x_{i+1}-x_i\|^2+K\sum_{i<m}\|x_{i+1}-x_i\|^3.$$
--
--   This is the telescoped form of the pointwise affine-modulus estimate and is suited to discretized paths and finite partitions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_taylorRemainderNormed_le_affine {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
--       {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
--       (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
--       (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x : ℕ → E) (m : ℕ) :
--       |taylorRemainderNormed f f' f'' x m|
--         ≤ A * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 2
--           + K * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 3
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/TaylorTwoModulus`](https://prove2.me/theorems/9de0d95a-7af7-4d8b-902e-7044b67e5df2).
--
--   Definition modules: [`LevyStochCalc/Brownian/TaylorTwoVector`](https://prove2.me/theorems/7b95962e-e11d-4fe9-a26b-01c2fa7c2715).
--
--   Supporting theorems: [`abs_sub_taylor_two_le_affine`](https://prove2.me/theorems/5ef92fc9-92b2-4b92-8d3b-5f15ef4f7c9a).
--
--   Previous: [`abs_sub_taylor_two_le_affine`](https://prove2.me/theorems/5ef92fc9-92b2-4b92-8d3b-5f15ef4f7c9a).
--
--   [Source excerpt, lines 167–173](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L167-L173) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L166-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.TaylorTwoModulus`, declaration `LevyStochCalc.abs_taylorRemainderNormed_le_affine`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem LevyStochCalc.abs_taylorRemainderNormed_le_affine_readable {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x : ℕ → E) (m : ℕ) :
    |taylorRemainderNormed f f' f'' x m|
      ≤ A * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 2
        + K * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 3 := by sorry
