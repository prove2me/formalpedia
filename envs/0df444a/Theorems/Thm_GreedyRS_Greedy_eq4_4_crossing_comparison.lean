-- Prove2me | Theorems.Thm_GreedyRS_Greedy_eq4_4_crossing_comparison
-- name    : GreedyRS.Greedy.eq4_4_crossing_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:00.692375+00:00
-- url     : https://prove2.me/theorems/15532867-1b0b-461e-a0d1-206f49a5c6b3
-- title:
--   (4.4), p. 15 — on {X̄₁* > μ₁ − γ₀}, N_i(X̄₁*) ≤ Ñ_i((γ − γ₀)/σ̄) for each inferior alternative i
-- statement:
--   Fix an inferior alternative $i\ge2$ with mean $\mu_i$ and variance $\sigma_i^2>0$, and constants $\gamma>0$, $\bar\sigma>0$, $\gamma_0\in(0,\gamma)$ with
--   $$\mu_1-\mu_i\ge\gamma,\qquad\sigma_i^2\le\bar\sigma^2.$$
--   Let $x_{1j}$, $x_{ij}$ be any observation sequences of alternatives $1$ and $i$, with running averages $\bar X_1(n)$, $\bar X_i(n)$, and let $\bar Z_i(n)=\frac1n\sum_{j=1}^n(x_{ij}-\mu_i)/\sigma_i$ be the running average of the standardized observations. If $\bar X_1^*=\min_{n\ge1}\bar X_1(n)>\mu_1-\gamma_0$, then
--   $$N_i\Bigl(\min_{n\ge1}\bar X_1(n)\Bigr)=\inf\Bigl\{n\ge1:\bar X_i(n)<\min_{n\ge1}\bar X_1(n)\Bigr\}\ \le\ \inf\Bigl\{n\ge1:\bar Z_i(n)<\frac{\gamma-\gamma_0}{\bar\sigma}\Bigr\}=\tilde N_i\Bigl(\frac{\gamma-\gamma_0}{\bar\sigma}\Bigr).\qquad(4.4)$$
--
--   The comparison is pathwise. Under normality the right-hand sides for $i=2,\dots,k$ are i.i.d. copies of $\tilde N((\gamma-\gamma_0)/\bar\sigma)$, whose mean is $C((\gamma-\gamma_0)/\bar\sigma)$ by Lemma 2; this is what makes the total crossing time grow linearly in $k$.
--
--   **Formalization Note** The statement is deterministic: it holds for every pair of observation sequences. "$\min_{n\ge1}\bar X_1(n)>\mu_1-\gamma_0$" means bounded below with infimum $>\mu_1-\gamma_0$, and the crossing level on the left is that infimum. Infinite crossing times are $\infty\in\mathbb N\cup\{\infty\}$. $\sigma_i$ is $\sqrt{v_i}$ with $v_i>0$. The paper's alternative $1$ is Lean's index $0$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 15, §4.2, (4.4)

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy
theorem eq4_4_crossing_comparison (x : ℕ → ℕ → ℝ) (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (γ σbar γ0 : ℝ) (hσbar : 0 < σbar) (hγ0 : γ0 ∈ Set.Ioo 0 γ)
    (i : ℕ) (hi : 1 ≤ i) (hgap : μ i ≤ μ 0 - γ) (hvar : (v i : ℝ) ≤ σbar ^ 2)
    (hvpos : 0 < v i)
    (hmin : AboveFrom (runMean x 0) 1 (μ 0 - γ0)) :
    crossBelow (runMean x i) (boundary (runMean x 0) 1) 1 ≤
      crossTime ((γ - γ0) / σbar) 1 (fun j => (x i j - μ i) / Real.sqrt (v i)) := by sorry
end GreedyRS.Greedy
