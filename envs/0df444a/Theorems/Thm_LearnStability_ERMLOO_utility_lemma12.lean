-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_utility_lemma12
-- name    : LearnStability.ERMLOO.utility_lemma12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:20:33.417713+00:00
-- url     : https://prove2.me/theorems/ce707375-8662-4fde-8e04-ca03006ddcb7
-- title:
--   Utility Lemma 12 — the mean of m i.i.d. variables bounded by B deviates from its expectation by at most B/√m in L¹
-- statement:
--   Let $X_1,\dots,X_m$ ($m\ge1$) be independent, identically distributed real random variables on a probability space with $|X_i|\le B$ almost surely, and let $X=\frac1m\sum_{i=1}^m X_i$. Then
--   $$\mathbb E\big[|X-\mathbb E[X]|\big]\le\frac{B}{\sqrt m}.$$
--
--   This is the elementary concentration estimate used to compare the empirical risk of a fixed hypothesis with its risk, for instance in Lemma 14 and Lemma 16.
--
--   **Formalization Note.** The bound $|X_i|\le B$ is required almost surely (the paper writes $|X_i|\le B$), each $X_i$ is measurable, independence is `iIndepFun`, and identical distribution is required pairwise.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2650, Utility Lemma 12

import Mathlib

open MeasureTheory ProbabilityTheory

namespace LearnStability.ERMLOO

theorem utility_lemma12 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 1 ≤ m) (X : Fin m → Ω → ℝ) (B : ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ)
    (hident : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hB : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ B) :
    ∫ ω, |(∑ i, X i ω) / m - ∫ ω', (∑ i, X i ω') / m ∂μ| ∂μ ≤ B / Real.sqrt m := by sorry

end LearnStability.ERMLOO
