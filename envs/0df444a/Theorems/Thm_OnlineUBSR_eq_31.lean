-- Prove2me | Theorems.Thm_OnlineUBSR_eq_31
-- name    : OnlineUBSR.eq_31
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:21.550965+00:00
-- url     : https://prove2.me/theorems/2d6f4d6f-a6cd-43c5-92f0-3aee8a8c559e
-- title:
--   (31), p.19 — logarithm and Basel bounds for $a_k=c/k$, with $\log\frac{n+1}{k+1}$
-- statement:
--   Let $c>0$, $n\in\mathbb N$ and $a_k=c/k$. Then
--
--   1. $\displaystyle\sum_{k=1}^na_k\ge c\log n$;
--   2. for every $0\le k\le n$, $\displaystyle\sum_{j=k+1}^na_j\ge c\log\frac{n+1}{k+1}$;
--   3. $\displaystyle\sum_{k=1}^na_k^2\le\frac{c^2\pi^2}{6}$;
--   4. for all real $z_0,\sigma,L_1$ and every $\mu_1>0$,
--
--   $$
--   z_0^2e^{-2\mu_1\sum_{k=1}^na_k+L_1^2\sum_{k=1}^na_k^2}+\sigma^2\sum_{k=1}^na_k^2e^{-2\mu_1\sum_{j=k+1}^na_j+L_1^2\sum_{j=k+1}^na_j^2}\le z_0^2e^{-2\mu_1c\log n+\frac{L_1^2c^2\pi^2}{6}}+\sigma^2\sum_{k=1}^na_k^2e^{-2\mu_1c\log\frac{n+1}{k+1}+\frac{L_1^2c^2\pi^2}{6}} .
--   $$
--
--   Clause 4 is the inequality (31), with $\log\frac{n+1}{k+1}$ in place of the page's $\log\frac{n}{k+1}$.
--
--   **Formalization Note** At $n=0$, $\log 0$ is $0$ in Lean and all sums are empty, so every clause still holds; the proof of Theorem 1 uses $n\ge1$.
--
--   Differences from the source:
--   - generalization: log(n/(k+1)) in (31) → log((n+1)/(k+1)) in clauses 2 and 4; reason: a larger lower bound on Σ_{j=k+1}^n a_j, so a smaller right side; it implies the page's (31), and the printed constant 2^{2µ₁c} of (6) needs it
--   - generalization: the inequality (31) → (31) together with the three bounds on the step-size sums it uses; reason: extra conclusions, all used on p.19
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §7.1, eq. (31) and the sentence after (32), p.19

import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR

/-- **The step-size sums for `a_k = c/k`, used in (31), p.19.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §7.1, (31), p.19: "≤ z²0 exp(−2µ1c log n + L²1c²π²/6) + σ² Σ_{k=1}^n a²k
exp(−2µ1c log(n/(k+1)) + L²1c²π²/6) (31) […] For the inequality in (31), we have used
Σ_{k=1}^n 1/k² ≤ Σ_{k=1}^∞ 1/k² = π²/6."

For `c > 0` and `n ∈ ℕ`, with `a_k = c/k`:
1. `Σ_{k=1}^n a_k ≥ c log n`;
2. for every `0 ≤ k ≤ n`, `Σ_{j=k+1}^n a_j ≥ c log((n+1)/(k+1))`;
3. `Σ_{k=1}^n a_k² ≤ c²π²/6`;
4. the inequality (31) itself, with `log((n+1)/(k+1))` in place of `log(n/(k+1))`: for all reals
   `z₀, σ, L₁` and `μ₁ > 0`,
   `z₀² exp(−2μ₁Σ_{k=1}^n a_k + L₁²Σ_{k=1}^n a_k²) + σ²Σ_{k=1}^n a_k² exp(−2μ₁Σ_{j=k+1}^n a_j + L₁²Σ_{j=k+1}^n a_j²)
   ≤ z₀² exp(−2μ₁c log n + L₁²c²π²/6) + σ²Σ_{k=1}^n a_k² exp(−2μ₁c log((n+1)/(k+1)) + L₁²c²π²/6)`.

**Formalization Note.** Clauses 2 and 4 are sharper than the page's `log(n/(k+1))` (since
`(n+1)/(k+1) ≥ n/(k+1)`), and it is what the printed constant `2^{2μ₁c}` of Theorem 1 needs.
At `n = 0` clause 1 reads `0 ≥ c · log 0 = 0` (Mathlib's `Real.log 0 = 0`); the theorem applies
it for `n ≥ 1`. -/
theorem eq_31
    (c : ℝ) (hc : 0 < c) (n : ℕ) :
    c * Real.log n ≤ ∑ k ∈ Finset.Icc 1 n, c / (k : ℝ) ∧
    (∀ k : ℕ, k ≤ n →
      c * Real.log (((n : ℝ) + 1) / ((k : ℝ) + 1)) ≤ ∑ j ∈ Finset.Icc (k + 1) n, c / (j : ℝ)) ∧
    ∑ k ∈ Finset.Icc 1 n, (c / (k : ℝ)) ^ 2 ≤ c ^ 2 * π ^ 2 / 6 ∧
    (∀ z₀ σ μ₁ L₁ : ℝ, 0 < μ₁ →
      z₀ ^ 2 * Real.exp (-2 * μ₁ * ∑ k ∈ Finset.Icc 1 n, c / (k : ℝ) +
          L₁ ^ 2 * ∑ k ∈ Finset.Icc 1 n, (c / (k : ℝ)) ^ 2) +
        σ ^ 2 * ∑ k ∈ Finset.Icc 1 n, (c / (k : ℝ)) ^ 2 *
          Real.exp (-2 * μ₁ * ∑ j ∈ Finset.Icc (k + 1) n, c / (j : ℝ) +
            L₁ ^ 2 * ∑ j ∈ Finset.Icc (k + 1) n, (c / (j : ℝ)) ^ 2) ≤
      z₀ ^ 2 * Real.exp (-2 * μ₁ * c * Real.log n + L₁ ^ 2 * c ^ 2 * π ^ 2 / 6) +
        σ ^ 2 * ∑ k ∈ Finset.Icc 1 n, (c / (k : ℝ)) ^ 2 *
          Real.exp (-2 * μ₁ * c * Real.log (((n : ℝ) + 1) / ((k : ℝ) + 1)) +
            L₁ ^ 2 * c ^ 2 * π ^ 2 / 6)) := by sorry

end OnlineUBSR
