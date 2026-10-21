-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_lemma_6
-- name    : NaiveLearn.OverMatch.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:32.203632+00:00
-- url     : https://prove2.me/theorems/8cee63c2-4811-47d7-9027-62e5825b127d
-- title:
--   Lemma 6, p. 23 — for small ϵ the extremization DeGroot process converges to the corner on the side of p where ⟨µ^W, x¹⟩ lies, with probability ≥ 1 − η
-- statement:
--   Let $0<p<1$, let $(\sigma_\delta)_{\delta\in(0,1]}$ be an extremization family for the prior $p$, and let $W$ be the weight matrix of a strongly connected network (row-stochastic, irreducible, $w_{ii}>0$) with centrality measure $\mu^W$. Consider the $(\epsilon,\delta)$-extremization DeGroot process: the random action process with decision rule $\sigma_\delta$ and the $\epsilon$-DeGroot recursion (1), started at $\mathbf x^1\in[0,1]^m$.
--
--   For every $\eta>0$ there is $\delta\in(0,1]$ such that, for all sufficiently small $\epsilon$ (there is $\epsilon_0>0$ such that for all $\epsilon\in(0,\epsilon_0)$ and all $\mathbf x^1\in[0,1]^m$):
--
--   1. if $\langle\mu^W,\mathbf x^1\rangle>p+\eta$, then $\Pr\big(\lim_{t\to\infty}\mathbf x^t=\mathbf 1\big)\ge1-\eta$;
--   2. if $\langle\mu^W,\mathbf x^1\rangle<p-\eta$, then $\Pr\big(\lim_{t\to\infty}\mathbf x^t=\mathbf 0\big)\ge1-\eta$.
--
--   This is the finite-network learning statement: Corollary 1 averages it over the random initial beliefs.
--
--   **Formalization Note** "For all sufficiently small $\epsilon$" is read uniformly in $\mathbf x^1\in[0,1]^m$, which is how Corollary 1 uses it (there $\mathbf x^1$ is random). One $\delta$ serves both parts.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 23, Lemma 6

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Lemma 6, p. 23: for the `(ε, δ)`-extremization DeGroot process, for every `η > 0` there is
`δ ∈ (0, 1]` such that, for all sufficiently small `ε` (uniformly in `x¹ ∈ [0, 1]^m`),
`⟨µ^W, x¹⟩ > p + η` implies `x^t → 1` with probability at least `1 − η`, and `⟨µ^W, x¹⟩ < p − η`
implies `x^t → 0` with probability at least `1 − η`. -/
theorem lemma_6 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ → ℝ)
    (hσ : IsExtremizationFamily p σ) {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∀ η : ℝ, 0 < η → ∃ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ ε0 : ℝ, 0 < ε0 ∧
      ∀ ε ∈ Set.Ioo (0 : ℝ) ε0, ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
        (p + η < ∑ i, μ i * x1 i →
          ENNReal.ofReal (1 - η) ≤
            coinLaw m {U | Tendsto (beliefAct (σ δ) ε W x1 U) atTop (𝓝 1)}) ∧
        (∑ i, μ i * x1 i < p - η →
          ENNReal.ofReal (1 - η) ≤
            coinLaw m {U | Tendsto (beliefAct (σ δ) ε W x1 U) atTop (𝓝 0)}) := by sorry

end NaiveLearn.OverMatch
