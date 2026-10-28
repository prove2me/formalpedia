-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sqrt_sum_sq_sum_le_readable
-- name    : FunctionalInequalities.KLS.BKL.sqrt_sum_sq_sum_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:09.044981+00:00
-- url     : https://prove2.me/theorems/f159c409-0b24-4a71-8718-4a4409e0445e
-- title:
--   Finite-Sum Euclidean Triangle Inequality
-- statement:
--   This is the finite-sum Minkowski inequality for coordinatewise square sums.
--
--   Let $\iota$ and $\kappa$ be finite types, let $s$ be a finite subset of $\kappa$, and let $f:\kappa\to\iota\to\mathbb{R}$. Then
--
--   $$
--   \sqrt{\sum_i\left(\sum_{q\in s}f(q,i)\right)^2}
--   \le
--   \sum_{q\in s}\sqrt{\sum_i f(q,i)^2}.
--   $$
--
--   This general finite-dimensional inequality is reused to separate mask contributions in cumulant-energy estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sqrt_sum_sq_sum_le {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℝ) :
--       Real.sqrt (∑ i, (∑ q ∈ s, f q i) ^ 2) ≤ ∑ q ∈ s, Real.sqrt (∑ i, f q i ^ 2)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086).
--
--   Previous: [`sum_selected_eq`](https://prove2.me/theorems/fa7bea17-a11a-4926-a7d5-5e7c584f47ec) · Next: [`sum_sq_pairTerm_ofFn_le`](https://prove2.me/theorems/dd204f83-a393-4ef0-af4b-7c00fc22f487).
--
--   [Source excerpt, lines 237–238](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L237-L238) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L236-L251 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, declaration `FunctionalInequalities.KLS.BKL.sqrt_sum_sq_sum_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic

theorem FunctionalInequalities.KLS.BKL.sqrt_sum_sq_sum_le_readable {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℝ) :
    Real.sqrt (∑ i, (∑ q ∈ s, f q i) ^ 2) ≤ ∑ q ∈ s, Real.sqrt (∑ i, f q i ^ 2) := by sorry
