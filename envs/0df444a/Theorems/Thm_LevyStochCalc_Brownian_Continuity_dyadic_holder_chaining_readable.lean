-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadic_holder_chaining_readable
-- name    : LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:24.028348+00:00
-- url     : https://prove2.me/theorems/749988d9-89e5-4fb5-9831-f2ad8915a549
-- title:
--   Deterministic Dyadic Hölder Chaining
-- statement:
--   This is the deterministic dyadic Hölder-chaining lemma. Let $f:\mathbb R\to\mathbb R$, $\alpha,C\in\mathbb R$, and $N\in\mathbb N$, with $\alpha>0$ and $C\ge0$. Assume that for every $n\ge N$, every integer $k$ with $0\le k$ and $k+1\le2^n$, the consecutive dyadic increment satisfies
--
--   $$
--   \left|f\!\left(\frac{k+1}{2^n}\right)-f\!\left(\frac{k}{2^n}\right)\right|
--   \le C\bigl((1/2)^\alpha\bigr)^n.
--   $$
--
--   Then there exists $K\ge0$ such that for all dyadic rationals $s,t\in[0,1]$ with $|s-t|\le(1/2)^N$,
--
--   $$
--   |f(s)-f(t)|\le K|s-t|^\alpha.
--   $$
--
--   This supplies the deterministic pathwise estimate used after obtaining eventual dyadic increment bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma dyadic_holder_chaining {f : ℝ → ℝ} {α C : ℝ} {N : ℕ}
--       (hα : 0 < α) (hC : 0 ≤ C)
--       (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
--         |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ C * ((1 / 2 : ℝ) ^ α) ^ n) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
--         0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → |s - t| ≤ (1 / 2 : ℝ) ^ N →
--         |f s - f t| ≤ K * |s - t| ^ α
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Supporting theorems: [`dyadicTrunc_eventually_eq`](https://prove2.me/theorems/3e1785d0-d93f-4be2-b07c-69e9627ca49e), [`dyadicTrunc_near_step`](https://prove2.me/theorems/cc514a95-7843-459b-984c-57d63cd24e90), [`dyadicTrunc_telescope`](https://prove2.me/theorems/d83ab303-32f8-4188-92ae-deae609712a4), [`exists_dyadic_scale`](https://prove2.me/theorems/1d383b87-9bce-4bea-947b-c6594626f115), [`rpow_half_pow_le`](https://prove2.me/theorems/4d94cc63-e21d-4250-be10-7ae322e82378).
--
--   Previous: [`kc_exponent_identity`](https://prove2.me/theorems/015b3d90-70b0-4878-af84-3becbce9c7eb).
--
--   [Source excerpt, lines 407–413](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L407-L413) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L402-L519 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining_readable {f : ℝ → ℝ} {α C : ℝ} {N : ℕ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ C * ((1 / 2 : ℝ) ^ α) ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
      0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → |s - t| ≤ (1 / 2 : ℝ) ^ N →
      |f s - f t| ≤ K * |s - t| ^ α := by sorry
