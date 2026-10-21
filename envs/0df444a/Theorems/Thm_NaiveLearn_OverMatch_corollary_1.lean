-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_corollary_1
-- name    : NaiveLearn.OverMatch.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:25.335716+00:00
-- url     : https://prove2.me/theorems/a82f6cbf-bb71-4ace-9397-87b2ac585655
-- title:
--   Corollary 1, p. 24 — on any network, for every r > 0 some (ϵ, δ)-extremization DeGroot process learns with probability ≥ l^G_F − r
-- statement:
--   Let $0<p<1$, let $F_0,F_1$ be probability measures on a measurable signal space, let $(\sigma_\delta)_{\delta\in(0,1]}$ be an extremization family for $p$, and let $W$ be the weight matrix of a strongly connected network (row-stochastic, irreducible, $w_{ii}>0$) with centrality measure $\mu^W$. Let
--   $$
--   l^G_F=p\,\Pr\Big(\sum_{i\in V}\mu^W_ix^1_i>p\ \Big|\ \omega=1\Big)+(1-p)\,\Pr\Big(\sum_{i\in V}\mu^W_ix^1_i<p\ \Big|\ \omega=0\Big),
--   $$
--   where $x^1_i$ is agent $i$'s posterior. Then for every $r>0$ there are $\delta\in(0,1]$ and $\epsilon\in(0,1]$ such that the $(\epsilon,\delta)$-extremization DeGroot process, with initial beliefs the agents' posteriors, satisfies
--   $$
--   \Pr\big[\exists\,t^*:\ a_i^t=\omega\ \text{for all }i\in V\text{ and all }t\ge t^*\big]\ \ge\ l^G_F-r ,
--   $$
--   i.e. $(1-l^G_F+r)$-naive learning in the sense of Definition 2.
--
--   Theorem 2 follows from this and the fact that $l^G_F\to1$ under vanishing influence.
--
--   **Formalization Note** The printed $l^G_F$ writes $x^0_i$ in its first term; it is the initial belief $x^1_i$, as in the corollary's proof. "$l^G_F-r$ naive learning" is read as learning with probability at least $l^G_F-r$. The probability is under the joint law of the state, the signals and the coins. Lean time $0$ is the paper's period $1$.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 24, Corollary 1 and the definition of l^G_F

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Corollary 1, p. 24: for every network and every `r > 0` there are `δ, ε ∈ (0, 1]` such that
the `(ε, δ)`-extremization DeGroot process learns the state with probability at least
`l^G_F − r`, i.e. satisfies `(1 − l^G_F + r)`-naive learning. -/
theorem corollary_1 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1]
    (σ : ℝ → ℝ → ℝ) (hσ : IsExtremizationFamily p σ)
    {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∀ r : ℝ, 0 < r → ∃ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ ε ∈ Set.Ioc (0 : ℝ) 1,
      NaiveLearning (1 - lGF p F0 F1 μ + r) (σ δ) ε p W F0 F1 := by sorry

end NaiveLearn.OverMatch
