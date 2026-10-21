-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_lemma_5
-- name    : NaiveLearn.OverMatch.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:26.178292+00:00
-- url     : https://prove2.me/theorems/e2e334ff-f351-4f58-828f-f046a2d4431f
-- title:
--   Lemma 5, p. 23 — started near the corner 1 (resp. 0), the ϵ-DeGroot process converges there and stays above (below) p with probability → 1
-- statement:
--   Let $0<p<1$ and let $W$ be the weight matrix of a strongly connected network (row-stochastic, irreducible, $w_{ii}>0$) with centrality measure $\mu^W$. Consider the $\epsilon$-DeGroot process (decision rule $\sigma(x)=x$) with initial belief $\mathbf x^1\in[0,1]^m$.
--
--   1. If $x^1_i>1-\eta$ for every $i$, let $A_\eta$ be the event that $\lim_{t\to\infty}\mathbf x^t=\mathbf 1$ and $x_i^t>p$ for every $i$ and every $t$.
--   2. If $x^1_i<\eta$ for every $i$, let $B_\eta$ be the event that $\lim_{t\to\infty}\mathbf x^t=\mathbf 0$ and $x_i^t<p$ for every $i$ and every $t$.
--
--   Then the probabilities of $A_\eta$ and $B_\eta$ approach one as $\eta\to0$, uniformly in $\epsilon\in(0,1]$ and in the initial belief: for every $\gamma>0$ there is $\eta_0>0$ such that for all $\eta\in(0,\eta_0)$, all $\epsilon\in(0,1]$ and all admissible $\mathbf x^1$,
--   $$
--   \Pr(A_\eta)\ge 1-\gamma\qquad\text{and}\qquad \Pr(B_\eta)\ge1-\gamma .
--   $$
--
--   Lemma 6 uses this, through a comparison of the two processes, to keep the extremization process at the corner once it gets close to it.
--
--   **Formalization Note** The paper's "approaches one as $\eta$ approaches zero" is read uniformly in $\epsilon$ and $\mathbf x^1$, which is what its proof gives (the bound $1-\eta/(\mu_*(1-p))$ does not depend on them) and how Lemma 6 uses it. Lean time $0$ is the paper's period $1$, so "every $t$" includes the initial belief.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 23, Lemma 5

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Lemma 5, p. 23: for the `ε`-DeGroot process (`σ = id`), started with every belief above
`1 − η`, the event `A_η` that `x^t → 1` and `x_i^t > p` for all `i` and all `t` has probability
tending to one as `η → 0`, uniformly in `ε ∈ (0, 1]` and in the initial belief; symmetrically for
beliefs below `η`, the limit `0` and `x_i^t < p`. -/
theorem lemma_5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ)
    (μ : Fin m → ℝ) (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∀ γ : ℝ, 0 < γ → ∃ η0 : ℝ, 0 < η0 ∧ ∀ η ∈ Set.Ioo (0 : ℝ) η0,
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
        ((∀ i, 1 - η < x1 i) →
          ENNReal.ofReal (1 - γ) ≤ coinLaw m {U |
            Tendsto (beliefAct id ε W x1 U) atTop (𝓝 1) ∧
              ∀ t i, p < beliefAct id ε W x1 U t i}) ∧
        ((∀ i, x1 i < η) →
          ENNReal.ofReal (1 - γ) ≤ coinLaw m {U |
            Tendsto (beliefAct id ε W x1 U) atTop (𝓝 0) ∧
              ∀ t i, beliefAct id ε W x1 U t i < p}) := by sorry

end NaiveLearn.OverMatch
