-- Prove2me | Theorems.Thm_GreedyRS_Greedy_theorem1_sample_optimality
-- name    : GreedyRS.Greedy.theorem1_sample_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:16.136748+00:00
-- url     : https://prove2.me/theorems/2693a812-57d9-4e2e-a0d9-b4d71acf5160
-- title:
--   Theorem 1, p. 15 — if c > C(γ/σ̄) and B = ck, then liminf_k PCS ≥ Pr{min_n X̄₁(n) > μ₁ − γ₀} = [C(γ₀/σ₁)]⁻¹ > 0
-- statement:
--   **Setting.** A fixed-budget ranking-and-selection problem has $k$ alternatives. Alternative $i$ produces independent observations $X_{i1},X_{i2},\dots\sim N(\mu_i,\sigma_i^2)$, with $\sigma_i^2>0$, independent across alternatives, and alternative $1$ is the best. The greedy procedure takes one observation from every alternative, then repeatedly takes one observation from the alternative with the largest current running average $\bar X_i(n_i)$ until the total number of observations is $B$, and selects the alternative with the largest final running average. The PCS is the probability that it selects alternative $1$. The asymptotic regime is $k\to\infty$ along one sequence $(\mu_i,\sigma_i^2)_{i\ge1}$, problem $k$ using its first $k$ alternatives.
--
--   **Assumption 1.** There are constants $\gamma>0$ and $\bar\sigma^2>0$ with $\mu_1-\max_{i\ge2}\mu_i\ge\gamma$ and $\max_i\sigma_i^2\le\bar\sigma^2$, regardless of how large $k$ is.
--
--   Let $\Phi$ be the standard normal distribution function and
--   $$C(x)=\exp\Bigl(\sum_{n=1}^\infty\frac1n\Phi(-\sqrt n\,x)\Bigr),\qquad x>0.$$
--
--   **Theorem.** Suppose Assumption 1 holds, the total budget is $B=ck$, and $c>C(\gamma/\bar\sigma)$. Then there is a constant $\gamma_0\in(0,\gamma)$ with $C\bigl((\gamma-\gamma_0)/\bar\sigma\bigr)=c$, and for every such $\gamma_0$ the PCS of the greedy procedure satisfies
--   $$\liminf_{k\to\infty}\mathrm{PCS}\ \ge\ \Pr\Bigl\{\min_{n\ge1}\bar X_1(n)>\mu_1-\gamma_0\Bigr\}=\Bigl[C\Bigl(\frac{\gamma_0}{\sigma_1}\Bigr)\Bigr]^{-1}>0.$$
--
--   The greedy procedure is therefore *sample optimal* (Definition 1 of the paper): a budget growing only linearly in the number of alternatives keeps the probability of correct selection bounded away from zero, with an explicit lower bound.
--
--   **Formalization Note**
--   1. The budget $B=ck$ is $\lfloor ck\rfloor$, since $ck$ need not be an integer.
--   2. Alternatives are indexed from $0$: Lean's alternative $0$ is the paper's alternative $1$, and $\sigma_1=\sqrt{v_0}$.
--   3. Ties in every arg max go to the smallest index (a probability-zero event under normality).
--   4. Variances are assumed positive, as the normalizations $\gamma_0/\sigma_1$ and $(\bar X_i(n)-\mu_i)/\sigma_i$ of the paper require; the whole observation array is mutually independent.
--   5. "$\min_{n\ge1}\bar X_1(n)>a$" means bounded below with infimum $>a$; the minimum is attained almost surely (Lemma 1).
--   6. The existence of $\gamma_0$, implicit on the page, is stated as a conclusion, so the bound cannot hold vacuously.
--   7. Every argument of $C$ ($\gamma/\bar\sigma$, $(\gamma-\gamma_0)/\bar\sigma$, $\gamma_0/\sigma_1$) is positive, where the series converges. Probabilities and the liminf are taken in $[0,\infty]$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 15, Theorem 1 (Assumption 1, p. 12); proof EC.1.3, pp. ec2–ec3

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy
theorem theorem1_sample_optimality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X)
    (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (c : ℝ) (hc : Cfun (γ / σbar) < c) :
    (∃ γ0 ∈ Set.Ioo 0 γ, Cfun ((γ - γ0) / σbar) = c) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ, Cfun ((γ - γ0) / σbar) = c →
      P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          ≤ Filter.liminf (fun k : ℕ => pcs P X k 1 ⌊c * k⌋₊) Filter.atTop ∧
      P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          = ENNReal.ofReal (1 / Cfun (γ0 / Real.sqrt (v 0))) ∧
      0 < P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)} := by sorry
end GreedyRS.Greedy
