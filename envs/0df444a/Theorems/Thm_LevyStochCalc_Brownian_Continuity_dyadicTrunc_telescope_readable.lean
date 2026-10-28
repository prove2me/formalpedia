-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_telescope_readable
-- name    : LevyStochCalc.Brownian.Continuity.dyadicTrunc_telescope_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:20.902006+00:00
-- url     : https://prove2.me/theorems/d83ab303-32f8-4188-92ae-deae609712a4
-- title:
--   Telescoping Dyadic Truncation Bound
-- statement:
--   Let f : ℝ → ℝ and b : ℕ → ℝ satisfy b(n) ≥ 0 and the consecutive dyadic increment bound at every level n ≥ N. For 0 ≤ x ≤ 1, m with N ≤ m+1, and L ≥ m,
--
--   $$|f(\operatorname{dyadicTrunc}(L,x))-f(\operatorname{dyadicTrunc}(m,x))|\le\sum_{n\in\{m+1,\ldots,L\}}b(n).$$
--
--   In Lean this sum is written over `Finset.Ico (m + 1) (L + 1)`. The lemma `dyadicTrunc_telescope_readable` is the multiscale chaining estimate obtained by accumulating the successive truncation bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma dyadicTrunc_telescope {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
--       (hb : ∀ n, 0 ≤ b n)
--       (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
--         |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
--       {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ} (hm : N ≤ m + 1) :
--       ∀ L, m ≤ L → |f (dyadicTrunc L x) - f (dyadicTrunc m x)|
--         ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Supporting theorems: [`dyadicTrunc_succ_step`](https://prove2.me/theorems/f1f03a2a-9f1b-43c6-84e0-395a9ea8ebbc).
--
--   Previous: [`dyadicTrunc_succ_step`](https://prove2.me/theorems/f1f03a2a-9f1b-43c6-84e0-395a9ea8ebbc) · Next: [`dyadicTrunc_near_step`](https://prove2.me/theorems/cc514a95-7843-459b-984c-57d63cd24e90).
--
--   [Source excerpt, lines 248–254](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L248-L254) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L245-L268 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadicTrunc_telescope`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.dyadicTrunc_telescope_readable {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ} (hm : N ≤ m + 1) :
    ∀ L, m ≤ L → |f (dyadicTrunc L x) - f (dyadicTrunc m x)|
      ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by sorry
