-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_succ_step_readable
-- name    : LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:30.306364+00:00
-- url     : https://prove2.me/theorems/f1f03a2a-9f1b-43c6-84e0-395a9ea8ebbc
-- title:
--   Successive Dyadic Truncation Step
-- statement:
--   Let f and b satisfy the nonnegative level bounds from `dyadicTrunc_near_step_readable`: for every n ≥ N and every admissible integer k, consecutive level-n dyadics have f-increment at most b(n). If n+1 ≥ N and 0 ≤ x ≤ 1, then
--
--   $$|f(\operatorname{dyadicTrunc}(n+1,x))-f(\operatorname{dyadicTrunc}(n,x))|\le b(n+1).$$
--
--   The lemma `dyadicTrunc_succ_step_readable` controls one refinement of the dyadic approximation.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma dyadicTrunc_succ_step {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
--       (hb : ∀ n, 0 ≤ b n)
--       (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
--         |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
--       {n : ℕ} (hn : N ≤ n + 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
--       |f (dyadicTrunc (n + 1) x) - f (dyadicTrunc n x)| ≤ b (n + 1)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Previous: [`dense_dyadicRationals`](https://prove2.me/theorems/85782cfc-fe1d-4e3d-b7b8-39bea04a659f) · Next: [`dyadicTrunc_telescope`](https://prove2.me/theorems/d83ab303-32f8-4188-92ae-deae609712a4).
--
--   [Source excerpt, lines 212–217](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L212-L217) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L209-L243 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step_readable {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {n : ℕ} (hn : N ≤ n + 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |f (dyadicTrunc (n + 1) x) - f (dyadicTrunc n x)| ≤ b (n + 1) := by sorry
