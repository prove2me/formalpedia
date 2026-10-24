-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_integral_sum_mul_of_condExp_eq_zero_408915f
-- name    : LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:43:40.319698+00:00
-- url     : https://prove2.me/theorems/1d301606-414e-41f5-95dd-a2eb03f833e8
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
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/MartingaleDifference.lean#L50-L72 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.MartingaleDifference`, declaration `LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/MartingaleDifference.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
open MeasureTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
section MartingaleDifference
variable (𝒢 : ℕ → MeasurableSpace Ω) (h𝒢le : ∀ k, 𝒢 k ≤ mΩ) (h𝒢mono : Monotone 𝒢)
  (Y : ℕ → Ω → ℝ) (hY : ∀ k, MemLp (Y k) 2 P)
  (hYmeas : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (Y k))
  (hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0)
include h𝒢le h𝒢mono hY hYmeas hYcond

theorem LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero_408915f (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂P = 0 := by sorry
