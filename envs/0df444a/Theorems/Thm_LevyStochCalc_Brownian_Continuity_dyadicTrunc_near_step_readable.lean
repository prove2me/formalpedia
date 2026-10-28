-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_near_step_readable
-- name    : LevyStochCalc.Brownian.Continuity.dyadicTrunc_near_step_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:24.617278+00:00
-- url     : https://prove2.me/theorems/cc514a95-7843-459b-984c-57d63cd24e90
-- title:
--   Dyadic Truncation Bound at One Scale
-- statement:
--   Let f : ℝ → ℝ, b : ℕ → ℝ with b(n) ≥ 0, and N : ℕ. Suppose that for every n ≥ N and every integer k with 0 ≤ k and k+1 ≤ 2ⁿ,
--
--   $$\left|f\!\left(\frac{k+1}{2^n}\right)-f\!\left(\frac{k}{2^n}\right)\right|\le b(n).$$
--
--   Then for m ≥ N and 0 ≤ s ≤ t ≤ 1 with t−s ≤ (1/2)^m,
--
--   $$|f(\operatorname{dyadicTrunc}(m,s))-f(\operatorname{dyadicTrunc}(m,t))|\le b(m).$$
--
--   This is the cross-point estimate that connects nearby points at a common dyadic scale.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma dyadicTrunc_near_step {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
--       (hb : ∀ n, 0 ≤ b n)
--       (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
--         |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
--       {m : ℕ} (hm : N ≤ m) {s t : ℝ} (hs0 : 0 ≤ s) (ht1 : t ≤ 1) (hst : s ≤ t)
--       (hclose : t - s ≤ (1 / 2) ^ m) :
--       |f (dyadicTrunc m s) - f (dyadicTrunc m t)| ≤ b m
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Previous: [`dyadicTrunc_telescope`](https://prove2.me/theorems/d83ab303-32f8-4188-92ae-deae609712a4) · Next: [`dyadicTrunc_eventually_eq`](https://prove2.me/theorems/3e1785d0-d93f-4be2-b07c-69e9627ca49e).
--
--   [Source excerpt, lines 273–279](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L273-L279) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L270-L308 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadicTrunc_near_step`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.dyadicTrunc_near_step_readable {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {m : ℕ} (hm : N ≤ m) {s t : ℝ} (hs0 : 0 ≤ s) (ht1 : t ≤ 1) (hst : s ≤ t)
    (hclose : t - s ≤ (1 / 2) ^ m) :
    |f (dyadicTrunc m s) - f (dyadicTrunc m t)| ≤ b m := by sorry
