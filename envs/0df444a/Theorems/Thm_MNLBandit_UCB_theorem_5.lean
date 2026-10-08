-- Prove2me | Theorems.Thm_MNLBandit_UCB_theorem_5
-- name    : MNLBandit.UCB.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:09:17.206982+00:00
-- url     : https://prove2.me/theorems/9860f12e-e23c-43a0-a1ca-c0d564c627d2
-- title:
--   Theorem 5, pp. 50–51 — multiplicative Chernoff bounds for the mean of n i.i.d. geometric variables
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be i.i.d. geometric random variables with parameter $p\in(0,1]$, i.e. $\Pr(X_i=m)=(1-p)^mp$ for $m=0,1,2,\dots$, and let $\mu=\mathbb E X_i=\frac{1-p}{p}$. For every $\delta>0$:
--   1. (upper tail)
--   $$
--   \Pr\Big(\frac1n\sum_{i=1}^nX_i>(1+\delta)\mu\Big)\le\begin{cases}\exp\Big(-\dfrac{n\mu\delta^2}{2(1+\delta)(1+\mu)^2}\Big)&\text{if }\mu\le1,\\[3mm]\exp\Big(-\dfrac{n\delta^2\mu^2}{6(1+\mu)^2}\Big(3-\dfrac{2\delta\mu}{1+\mu}\Big)\Big)&\text{if }\mu\ge1\text{ and }\delta\in(0,1);\end{cases}
--   $$
--   2. (lower tail)
--   $$
--   \Pr\Big(\frac1n\sum_{i=1}^nX_i<(1-\delta)\mu\Big)\le\begin{cases}\exp\Big(-\dfrac{n\delta^2\mu}{6(1+\mu)^2}\Big(3-\dfrac{2\delta\mu}{1+\mu}\Big)\Big)&\text{if }\mu\le1,\\[3mm]\exp\Big(-\dfrac{n\delta^2\mu^2}{2(1+\mu)^2}\Big)&\text{if }\mu\ge1.\end{cases}
--   $$
--   The two cases overlap at $\mu=1$, where both bounds hold. These are the paper's extension of the multiplicative Chernoff–Hoeffding bounds to unbounded (geometric) variables; they drive the concentration of the epoch averages in Lemma A.2.
--
--   **Formalization Note.** The sample is the product measure of $n$ copies of Mathlib's `geometricMeasure p`, whose mass at $m$ is $(1-p)^mp$, exactly the paper's convention. The paper leaves the range of $\delta$ implicit in three of the four cases; $\delta>0$ is required (for $\delta\in(-1,0)$ the first bound fails). For $\delta\ge1$ the lower-tail event is empty.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, pp. 50–51, Theorem 5

import Mathlib

namespace MNLBandit.UCB

open MeasureTheory ProbabilityTheory

theorem theorem_5 (n : ℕ) (hn : 1 ≤ n) (p : unitInterval) (hp : p ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    let μ : ℝ := (1 - (p : ℝ)) / (p : ℝ)
    let P : Measure (Fin n → ℕ) := Measure.pi (fun _ : Fin n => geometricMeasure p)
    let Xbar : (Fin n → ℕ) → ℝ := fun x => (∑ k, (x k : ℝ)) / (n : ℝ)
    (μ ≤ 1 → P {x | Xbar x > (1 + δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * μ * δ ^ 2) / (2 * (1 + δ) * (1 + μ) ^ 2)))) ∧
    (1 ≤ μ → δ < 1 → P {x | Xbar x > (1 + δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ ^ 2 / (6 * (1 + μ) ^ 2))
          * (3 - 2 * δ * μ / (1 + μ))))) ∧
    (μ ≤ 1 → P {x | Xbar x < (1 - δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ / (6 * (1 + μ) ^ 2))
          * (3 - 2 * δ * μ / (1 + μ))))) ∧
    (1 ≤ μ → P {x | Xbar x < (1 - δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ ^ 2) / (2 * (1 + μ) ^ 2)))) := by sorry

end MNLBandit.UCB
