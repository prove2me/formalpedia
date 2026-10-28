-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_ite_mul_sum_ite_readable
-- name    : LevyStochCalc.Brownian.Ito.sum_ite_mul_sum_ite_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:49.408831+00:00
-- url     : https://prove2.me/theorems/7b3182dd-5410-4504-8fdb-fdf2d08f8bb4
-- title:
--   Product of Step Sums on a Strict Partition
-- statement:
--   Let $π:Fin(M+1)→ℝ$ be strictly monotone, let $f,g:Fin\,M→ℝ$, and let $s∈ℝ$. At most one partition cell $(π(j),π(j+1)]$ contains $s$. Consequently,
--
--   $$\left(\sum_j\mathbf{1}_{(π_j,π_{j+1}]}(s)f_j\right)\left(\sum_j\mathbf{1}_{(π_j,π_{j+1}]}(s)g_j\right)
--   =\sum_j\mathbf{1}_{(π_j,π_{j+1}]}(s)f_jg_j.$$
--
--   This is a finite algebraic identity for step functions and is independent of measure-theoretic assumptions. It underlies evaluation of products of simple predictable integrands.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_ite_mul_sum_ite {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
--       (f g : Fin M → ℝ) (s : ℝ) :
--       (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
--         * (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g j else 0)
--         = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j * g j else 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraProduct`](https://prove2.me/theorems/99205bea-847c-43ba-a041-1e0384d4d19c).
--
--   Next: [`SimplePredictable.eval_mul_on_common`](https://prove2.me/theorems/0eb3f171-e89b-4176-adbc-20be9554ddb1).
--
--   [Source excerpt, lines 28–32](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L28-L32) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L26-L57 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraProduct`, declaration `LevyStochCalc.Brownian.Ito.sum_ite_mul_sum_ite`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u

theorem LevyStochCalc.Brownian.Ito.sum_ite_mul_sum_ite_readable {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f g : Fin M → ℝ) (s : ℝ) :
    (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      * (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j * g j else 0 := by sorry
