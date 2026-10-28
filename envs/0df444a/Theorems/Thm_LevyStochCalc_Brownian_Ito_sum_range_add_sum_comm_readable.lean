-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_range_add_sum_comm_readable
-- name    : LevyStochCalc.Brownian.Ito.sum_range_add_sum_comm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:18.71123+00:00
-- url     : https://prove2.me/theorems/3691605f-5bd6-4983-af72-18ade5e5f6bc
-- title:
--   Reordering a Split Triple Sum
-- statement:
--   This is a finite-sum rearrangement identity.
--
--   For natural numbers $n,d,m$, let $A:\operatorname{Fin}(n)\times\mathbb N\to\mathbb R$ and $B_c:\operatorname{Fin}(n)\times\operatorname{Fin}(d)\times\mathbb N\to\mathbb R$. Then
--   $$
--   \sum_{i<m}\sum_{p<n}\left(A_{p,i}+\sum_{k<d}B_{p,k,i}\right)
--   =
--   \sum_{p<n}\sum_{i<m}A_{p,i}
--   +\sum_{p<n}\sum_{k<d}\sum_{i<m}B_{p,k,i}.
--   $$
--
--   This elementary identity is used to separate drift and stochastic contributions after expanding a vector increment.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_range_add_sum_comm (m : ℕ) (A : Fin n → ℕ → ℝ) (Bc : Fin n → Fin d → ℕ → ℝ) :
--       ∑ i ∈ Finset.range m, ∑ p : Fin n, (A p i + ∑ k : Fin d, Bc p k i)
--         = (∑ p : Fin n, ∑ i ∈ Finset.range m, A p i)
--           + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m, Bc p k i
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoFormulaDecomp`](https://prove2.me/theorems/8f8fed5f-bb75-4985-83e7-6765eeac8110).
--
--   Next: [`sum_apply_fderiv₂_eq`](https://prove2.me/theorems/e68e16a1-d8ff-49b3-9798-30a9e8ff8724).
--
--   [Source excerpt, lines 38–41](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L38-L41) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L37-L55 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoFormulaDecomp`, declaration `LevyStochCalc.Brownian.Ito.sum_range_add_sum_comm`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {n d : ℕ}

theorem LevyStochCalc.Brownian.Ito.sum_range_add_sum_comm_readable (m : ℕ) (A : Fin n → ℕ → ℝ) (Bc : Fin n → Fin d → ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ p : Fin n, (A p i + ∑ k : Fin d, Bc p k i)
      = (∑ p : Fin n, ∑ i ∈ Finset.range m, A p i)
        + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m, Bc p k i := by sorry
