-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_posterior_mean_gt_lt
-- name    : NaiveLearn.OverMatch.posterior_mean_gt_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:16.516515+00:00
-- url     : https://prove2.me/theorems/846cf420-ae24-4143-ab21-516b6957887f
-- title:
--   Proof of Theorem 2, p. 24 — for a nontrivial information structure, E[x¹_i | ω = 1] > p and E[x¹_i | ω = 0] < p
-- statement:
--   Let $0<p<1$ be the prior of state $\omega=1$, and let $F_0,F_1$ be probability measures on a measurable signal space $S$ with $F_0\neq F_1$. Let $x^1(s)=\Pr[\omega=1\mid s]$ be the Bayesian posterior of a signal $s$. Then
--   $$
--   \mathbb E[x^1_i\mid\omega=1]=\int_S x^1(s)\,dF_1(s)>p
--   \qquad\text{and}\qquad
--   \mathbb E[x^1_i\mid\omega=0]=\int_S x^1(s)\,dF_0(s)<p .
--   $$
--
--   An informative signal moves the posterior towards the true state on average; with the weighted law of large numbers this places the centrality-weighted initial belief on the correct side of $p$ in large networks.
--
--   **Formalization Note** The hypothesis $F_0\neq F_1$ (a nontrivial information structure) is added: for $F_0=F_1$ the posterior equals $p$ almost surely and both inequalities fail. The paper calls such a structure "nontrivial" (p. 11) and cites this fact from Acemoglu et al. The posterior is the Radon–Nikodym derivative $d(pF_1)/d(pF_1+(1-p)F_0)$.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 24, proof of Theorem 2

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Proof of Theorem 2, p. 24: for a nontrivial information structure (`F₀ ≠ F₁`) the
first-period belief has conditional mean above the prior in state `1` and below it in state `0`:
`E[x¹_i | ω = 1] > p` and `E[x¹_i | ω = 0] < p`. -/
theorem posterior_mean_gt_lt (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1] (hF : F0 ≠ F1) :
    p < ∫ s, posterior p F0 F1 s ∂F1 ∧ ∫ s, posterior p F0 F1 s ∂F0 < p := by sorry

end NaiveLearn.OverMatch
