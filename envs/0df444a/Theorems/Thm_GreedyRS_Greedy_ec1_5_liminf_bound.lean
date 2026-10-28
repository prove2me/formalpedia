-- Prove2me | Theorems.Thm_GreedyRS_Greedy_ec1_5_liminf_bound
-- name    : GreedyRS.Greedy.ec1_5_liminf_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:02.528351+00:00
-- url     : https://prove2.me/theorems/d294d533-fa6a-48b1-a178-1d98d3a36e0a
-- title:
--   (EC.1.2), (EC.1.5), p. ec3 — liminf PCS ≥ Pr{min X̄₁(n) > μ₁ − γ_ϵ⁻} − Pr{argmin X̄₁(n) = ∞} for C((γ − γ_ϵ⁻)/σ̄) = c − 2ϵ
-- statement:
--   Work in the normal model of the paper: alternatives $i=1,2,\dots$ have independent $N(\mu_i,\sigma_i^2)$ observations with $\sigma_i^2>0$, and problem $k$ uses alternatives $1,\dots,k$. Suppose Assumption 1 holds: there are constants $\gamma>0$ and $\bar\sigma>0$ with $\mu_1-\mu_i\ge\gamma$ for every $i\ge2$ and $\sigma_i^2\le\bar\sigma^2$ for every $i$. Let
--   $$C(x)=\exp\Bigl(\sum_{n=1}^\infty\frac1n\Phi(-\sqrt n\,x)\Bigr),\qquad x>0,$$
--   let $c>C(\gamma/\bar\sigma)$, and let the budget of problem $k$ be $B=ck$. Choose $\epsilon$ with $0<2\epsilon<c-C(\gamma/\bar\sigma)$. Then there is a constant $\gamma_\epsilon^-\in(0,\gamma)$ with
--   $$C\Bigl(\frac{\gamma-\gamma_\epsilon^-}{\bar\sigma}\Bigr)=c-2\epsilon,\qquad(\mathrm{EC}.1.2)$$
--   and for every such $\gamma_\epsilon^-$ the PCS of the greedy procedure satisfies
--   $$\liminf_{k\to\infty}\mathrm{PCS}\ \ge\ \Pr\Bigl\{\min_{n\ge1}\bar X_1(n)>\mu_1-\gamma_\epsilon^-\Bigr\}-\Pr\Bigl\{\operatorname*{arg\,min}_{n\ge1}\bar X_1(n)=\infty\Bigr\}.\qquad(\mathrm{EC}.1.5)$$
--
--   This is the penultimate step of the proof of Theorem 1: letting $\epsilon\to0$ and using Lemma 1 to remove the second probability yields the theorem.
--
--   **Formalization Note** The budget $B=ck$ is $\lfloor ck\rfloor$. The paper's alternative $1$ is Lean's index $0$; one infinite sequence of means and variances serves every $k$. Ties go to the smallest index. "$\min>a$" means bounded below with infimum $>a$; the argmin is valued in $\mathbb N\cup\{\infty\}$. Probabilities and the liminf are in $[0,\infty]$, where the difference is truncated at $0$. The existence of $\gamma_\epsilon^-$, which the page asserts, is part of the conclusion, so the bound cannot hold vacuously. All arguments of $C$ are positive.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, pp. ec2–ec3, proof of Theorem 1 (EC.1.3), (EC.1.2) and (EC.1.5)

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy
theorem ec1_5_liminf_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X)
    (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (c : ℝ) (hc : Cfun (γ / σbar) < c)
    (ε : ℝ) (hε : 0 < 2 * ε ∧ 2 * ε < c - Cfun (γ / σbar)) :
    (∃ γε ∈ Set.Ioo 0 γ, Cfun ((γ - γε) / σbar) = c - 2 * ε) ∧
    ∀ γε ∈ Set.Ioo 0 γ, Cfun ((γ - γε) / σbar) = c - 2 * ε →
      P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γε)}
          - P {ω | argminFrom (runMean (fun i j => X i j ω) 0) 1 = ⊤}
        ≤ Filter.liminf (fun k : ℕ => pcs P X k 1 ⌊c * k⌋₊) Filter.atTop := by sorry
end GreedyRS.Greedy
