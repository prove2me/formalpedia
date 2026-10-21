-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_weighted_lln
-- name    : NaiveLearn.OverMatch.weighted_lln
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:30.157981+00:00
-- url     : https://prove2.me/theorems/c31616ad-26f1-45a4-ba3b-6b760eb9f306
-- title:
--   Proof of Theorem 2, p. 24 — under vanishing influence, P(Σ µ_i x¹_i > p | ω = 1) → 1 and P(Σ µ_i x¹_i < p | ω = 0) → 1
-- statement:
--   Let $0<p<1$, and let $F_0\neq F_1$ be probability measures on a measurable signal space $S$, with $x^1(s)$ the posterior of state $1$ given the signal $s$. Let $(\mu^k)_{k\in\mathbb N}$ be probability vectors, $\mu^k$ on $n_k$ agents, whose maximal coordinate vanishes, $\max_i\mu^k_i\to0$. If the signals $s_1,\dots,s_{n_k}$ are i.i.d. with law $F_\omega$ given the state, then
--   $$
--   \lim_{k\to\infty}\Pr\Big(\sum_{i}\mu^k_ix^1_i>p\ \Big|\ \omega=1\Big)=1
--   \qquad\text{and}\qquad
--   \lim_{k\to\infty}\Pr\Big(\sum_{i}\mu^k_ix^1_i<p\ \Big|\ \omega=0\Big)=1 .
--   $$
--
--   This is the Golub–Jackson weighted law of large numbers applied to the posteriors; it shows $l^{G_k}_F\to1$ along a vanishing-influence sequence.
--
--   **Formalization Note** The printed second limit lacks "$=1$"; it is stated with $1$, as the conclusion $\lim l^{G_m}_F=1$ requires. Only the weight vectors are needed, not the matrices. $F_0\neq F_1$ is the nontrivial-information hypothesis, without which both limits fail. With every coordinate of $\mu^k$ nonnegative and summing to one, each $n_k\ge1$.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 24, proof of Theorem 2

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Proof of Theorem 2, p. 24 (after Golub–Jackson): along any sequence of weight vectors `µ^k`
(probability vectors on `n k` agents) with vanishing maximal coordinate,
`P(Σ_i µ^k_i x¹_i > p | ω = 1) → 1` and `P(Σ_i µ^k_i x¹_i < p | ω = 0) → 1`, where the `x¹_i` are
the posteriors of i.i.d. signals with law `F_ω`. -/
theorem weighted_lln (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1] (hF : F0 ≠ F1)
    (n : ℕ → ℕ) (μ : ∀ k, Fin (n k) → ℝ) (hμ0 : ∀ k i, 0 ≤ μ k i) (hμ1 : ∀ k, ∑ i, μ k i = 1)
    (hvan : Tendsto (fun k => ⨆ i, μ k i) atTop (𝓝 0)) :
    Tendsto (fun k => (Measure.pi fun _ : Fin (n k) => F1)
        {s | p < ∑ i, μ k i * posterior p F0 F1 (s i)}) atTop (𝓝 1) ∧
    Tendsto (fun k => (Measure.pi fun _ : Fin (n k) => F0)
        {s | ∑ i, μ k i * posterior p F0 F1 (s i) < p}) atTop (𝓝 1) := by sorry

end NaiveLearn.OverMatch
