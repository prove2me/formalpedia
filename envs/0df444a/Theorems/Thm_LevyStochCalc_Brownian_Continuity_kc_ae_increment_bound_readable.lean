-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_ae_increment_bound_readable
-- name    : LevyStochCalc.Brownian.Continuity.kc_ae_increment_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:25.202807+00:00
-- url     : https://prove2.me/theorems/87c978a6-33c4-4d46-8fa8-81294193f4ae
-- title:
--   Almost-Everywhere Dyadic Increment Bound
-- statement:
--   This is the almost-sure dyadic increment estimate for a Kolmogorov process. Let $(\Omega,P)$ be a probability space, $X:\mathbb R\to\Omega\to\mathbb R$, $p,q\in\mathbb R$, $M\in\mathbb R_{\ge0}$, and assume `IsKolmogorovProcess X P p q M`. If $\alpha p<q-1$, then for $P$-almost every $\omega$ there exists $N\in\mathbb N$ such that for every $n\ge N$ and every integer $k$ with $0\le k$ and $k+1\le2^n$,
--
--   $$
--   \left|X\!\left(\frac{k+1}{2^n},\omega\right)-X\!\left(\frac{k}{2^n},\omega\right)\right|
--   \le\bigl((1/2)^\alpha\bigr)^n.
--   $$
--
--   This is the probabilistic input for `dyadic_holder_chaining_readable`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma kc_ae_increment_bound
--       (P : Measure Ω) [IsProbabilityMeasure P]
--       (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
--       (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
--       {α : ℝ} (hαpq : α * p < q - 1) :
--       ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
--         |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|
--           ≤ ((1 / 2 : ℝ) ^ α) ^ n
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityKolmogorovBounds`](https://prove2.me/theorems/db501a14-f954-4e21-a7e6-2ee411f6aff8).
--
--   Supporting theorems: [`kc_level_bad_measure`](https://prove2.me/theorems/0aab2f8f-d712-4737-86f0-b7eebb793739).
--
--   Previous: [`exists_tendsto_of_local_holder`](https://prove2.me/theorems/46c83da3-bc37-4fcf-a556-d68a3d13e420) · Next: [`kc_ae_interval_holder`](https://prove2.me/theorems/4c8f4cad-b521-472c-8c8e-9ef103021114).
--
--   [Source excerpt, lines 227–234](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L227-L234) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L223-L269 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kc_ae_increment_bound`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityKolmogorovBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Continuity.kc_ae_increment_bound_readable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|
        ≤ ((1 / 2 : ℝ) ^ α) ^ n := by sorry
