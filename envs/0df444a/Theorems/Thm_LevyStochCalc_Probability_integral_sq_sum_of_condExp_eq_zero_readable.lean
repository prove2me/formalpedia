-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_sq_sum_of_condExp_eq_zero_readable
-- name    : LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:27.694159+00:00
-- url     : https://prove2.me/theorems/fbb3abb4-5edb-4d91-878c-9d2326ca20d8
-- title:
--   Second Moment of a Sum of Martingale Differences
-- statement:
--   This theorem identifies the second moment of a finite sum of martingale differences with the sum of their second moments.
--
--   Let $P$ be a probability measure, let $(\mathcal G_k)_{k\in\mathbb N}$ be an increasing family of measurable spaces dominated by the ambient measurable space, and let $Y_k:\Omega\to\mathbb R$. Assume every $Y_k$ is in $L^2(P)$, is strongly measurable, and satisfies $\mathbb E[Y_k\mid\mathcal G_k]=0$ almost everywhere. For every $n\in\mathbb N$,
--
--   $$
--   \int\left(\sum_{i<n}Y_i\right)^2dP
--   =\sum_{i<n}\int Y_i^2\,dP.
--   $$
--
--   This is the finite orthogonality identity used to control sums of centered stochastic increments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sq_sum_of_condExp_eq_zero (n : ℕ) :
--       ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
--         = ∑ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/MartingaleDifference`](https://prove2.me/theorems/11d45bb7-a48e-4057-92a2-d82e2c13aef6).
--
--   Supporting theorems: [`integral_sum_mul_of_condExp_eq_zero`](https://prove2.me/theorems/0ce8f8fe-bada-4a95-91b2-50643f3abca3).
--
--   Previous: [`integral_sum_mul_of_condExp_eq_zero`](https://prove2.me/theorems/0ce8f8fe-bada-4a95-91b2-50643f3abca3).
--
--   [Source excerpt, lines 77–79](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/MartingaleDifference.lean#L77-L79) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/MartingaleDifference.lean#L74-L112 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.MartingaleDifference`, declaration `LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_MartingaleDifference

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/MartingaleDifference.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable (𝒢 : ℕ → MeasurableSpace Ω) (h𝒢le : ∀ k, 𝒢 k ≤ mΩ) (h𝒢mono : Monotone 𝒢)
  (Y : ℕ → Ω → ℝ) (hY : ∀ k, MeasureTheory.MemLp (Y k) 2 P)
  (hYmeas : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (Y k))
  (hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0)
include h𝒢le h𝒢mono hY hYmeas hYcond

theorem LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero_readable (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      = ∑ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P := by sorry
