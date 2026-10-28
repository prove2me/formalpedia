-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_sum_mul_of_condExp_eq_zero_readable
-- name    : LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:28.427983+00:00
-- url     : https://prove2.me/theorems/0ce8f8fe-bada-4a95-91b2-50643f3abca3
-- title:
--   Orthogonality of a Partial Sum and the Next Difference
-- statement:
--   This theorem states that a partial sum of martingale differences is orthogonal to the next difference.
--
--   Let $P$ be a probability measure on $\Omega$, let $(\mathcal G_k)_{k\in\mathbb N}$ be an increasing family of measurable spaces dominated by the ambient measurable space, and let $Y_k:\Omega\to\mathbb R$. Assume:
--
--   1. every $Y_k$ belongs to $L^2(P)$;
--   2. every $Y_k$ is strongly measurable in the ambient space;
--   3. $\mathbb E[Y_k\mid\mathcal G_k]=0$ almost everywhere.
--
--   Then, for every $n\in\mathbb N$,
--
--   $$
--   \int\left(\sum_{i<n}Y_i\right)Y_n\,dP=0.
--   $$
--
--   The conditional expectation is the Lean definition `condExp`; the result is a general martingale-difference orthogonality tool.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sum_mul_of_condExp_eq_zero (n : ℕ) :
--       ∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂P = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/MartingaleDifference`](https://prove2.me/theorems/11d45bb7-a48e-4057-92a2-d82e2c13aef6).
--
--   Next: [`integral_sq_sum_of_condExp_eq_zero`](https://prove2.me/theorems/fbb3abb4-5edb-4d91-878c-9d2326ca20d8).
--
--   [Source excerpt, lines 52–53](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/MartingaleDifference.lean#L52-L53) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/MartingaleDifference.lean#L50-L72 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.MartingaleDifference`, declaration `LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero_readable (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂P = 0 := by sorry
