-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_theorem_2
-- name    : NaiveLearn.OverMatch.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:31.419985+00:00
-- url     : https://prove2.me/theorems/0f99aa54-d5cc-46bb-97ec-c6e09ccfec35
-- title:
--   Theorem 2, p. 11 — under vanishing influence, some (ϵ_m, δ_m)-extremization DeGroot processes achieve naive learning
-- statement:
--   Let $0<p<1$ be the prior of state $\omega=1$, let $F_0\neq F_1$ be probability measures on a measurable signal space (a nontrivial information structure), and let $(\sigma_\delta)_{\delta\in(0,1]}$ be an extremization family for $p$. Let $(W_k)_{k\in\mathbb N}$ be weight matrices of strongly connected networks (row-stochastic, irreducible, $w_{ii}>0$), $W_k$ on $n_k$ agents, with centrality measures $\mu_k=\mu^{W_k}$ satisfying **vanishing influence**:
--   $$
--   \lim_{k\to\infty}\ \max_{i}\,[\mu_k]_i=0 .
--   $$
--   Then there are $(\epsilon_k,\delta_k)\in(0,1]^2$ for which naive learning holds: there is a sequence $\eta_k\to0$ such that, for every $k$, the $(\epsilon_k,\delta_k)$-extremization DeGroot process on the $k$-th network, with initial beliefs the agents' Bayesian posteriors, satisfies $\eta_k$-naive learning,
--   $$
--   \Pr\big[\exists\,t^*:\ a_i^t=\omega\ \text{for all agents } i \text{ and all } t\ge t^*\big]\ \ge\ 1-\eta_k .
--   $$
--
--   Probability matching ($\sigma(x)=x$) yields agreement but its agreement action equals the state with a probability bounded away from one; the theorem shows that a slight over-matching of the agents' beliefs, with suitable inertia, makes the eventual consensus action equal to the state with probability tending to one in large networks without dominant agents.
--
--   **Formalization Note** Two hypotheses are added to the page and both are used by its proof: $F_0\neq F_1$ with $0<p<1$ (for an uninformative structure the posterior is $p$ and learning fails), and uniform convergence $\sigma_\delta\to\mathrm{id}$ on $[0,1]$ in place of pointwise convergence (property 3, p. 7; the proof of Lemma 4 uses uniformity). The family $(\sigma_\delta)$ is arbitrary and fixed in advance; only $(\epsilon_k,\delta_k)$ are chosen. The networks may have arbitrary sizes $n_k$ (the paper overloads $m$); vanishing influence forces $n_k\to\infty$. The maximum of $\mu_k$ is a supremum over a nonempty finite index set, since $\mu_k$ is a probability vector. Probabilities are under the joint law of the state, the signals and the action coins; Lean time $0$ is the paper's period $1$.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 11, Theorem 2; Definitions 2–3, p. 10

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Theorem 2, p. 11: for any sequence of networks whose weight matrices `W_k` satisfy vanishing
influence (`max_i µ^{W_k}_i → 0`), there are `(ε_k, δ_k) ∈ (0, 1]²` such that the
`(ε_k, δ_k)`-extremization DeGroot processes achieve naive learning: they satisfy `η_k`-naive
learning for a sequence `η_k → 0`. -/
theorem theorem_2 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1] (hF : F0 ≠ F1)
    (σ : ℝ → ℝ → ℝ) (hσ : IsExtremizationFamily p σ)
    (n : ℕ → ℕ) (W : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ) (μ : ∀ k, Fin (n k) → ℝ)
    (hW : ∀ k, IsWeightMatrix (W k)) (hμ : ∀ k, IsCentrality (W k) (μ k))
    (hvan : Tendsto (fun k => ⨆ i, μ k i) atTop (𝓝 0)) :
    ∃ ε δ : ℕ → ℝ, (∀ k, ε k ∈ Set.Ioc (0 : ℝ) 1 ∧ δ k ∈ Set.Ioc (0 : ℝ) 1) ∧
      ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
        ∀ k, NaiveLearning (η k) (σ (δ k)) (ε k) p (W k) F0 F1 := by sorry

end NaiveLearn.OverMatch
