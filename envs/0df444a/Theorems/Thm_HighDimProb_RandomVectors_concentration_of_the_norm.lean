-- Prove2me | Theorems.Thm_HighDimProb_RandomVectors_concentration_of_the_norm
-- name    : HighDimProb.RandomVectors.concentration_of_the_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-18T06:41:43.571673+00:00
-- url     : https://prove2.me/theorems/a0785418-5e14-40c2-9ddc-cadaffdf0bd0
-- title:
--   Theorem 3.1.1 — Concentration of the norm
-- statement:
--   This is **Theorem 3.1.1**, the chapter's opening result and the warm-up for its
--   probabilistic toolkit: the Euclidean norm of a random vector with independent, sub-gaussian,
--   unit-variance coordinates concentrates tightly around $\sqrt n$, with fluctuations of only
--   constant order.
--
--   There is an absolute constant $C > 0$ such that the following holds. Let
--   $(\Omega, \mathcal F, P)$ be a probability space, $n \in \mathbb N$, and let $X = (X_1,
--   \dots, X_n) : \Omega \to \mathbb R^n$ be a random vector with independent, sub-gaussian
--   coordinates $X_i$ satisfying $\mathbb E X_i^2 = 1$. Writing $K = \max_i \|X_i\|_{\psi_2}$
--   for the largest sub-gaussian (Orlicz $\psi_2$) norm of a coordinate,
--
--   $$
--   \bigl\| \, \|X\|_2 - \sqrt n \, \bigr\|_{\psi_2} \;\le\; C K^2 .
--   $$
--
--   This says $\|X\|_2$ is concentrated in a window of width $O(K^2)$ around $\sqrt n$ — a
--   *constant*-width window, not one growing with $n$ — even though $\|X\|_2^2$ itself only
--   concentrates to within $O(\sqrt n)$ of its mean $n$; the square root compresses the
--   fluctuation. This concentration underlies the book's later observation that the standard
--   Gaussian distribution in high dimensions is close to the uniform distribution on a sphere.
--
--   **Formalization Note** The sub-gaussian norm $\|\cdot\|_{\psi_2}$ is
--   `HighDimProb.Concentration.SubgaussianNorm`, the series' published definition (from the
--   `01-concentration` mission), reused here rather than redeclared, per this series' policy of
--   reusing published definitions. Sub-gaussianity of each coordinate is stated explicitly as a
--   hypothesis (the existence of a finite exponential moment bound), rather than left implicit in
--   $K$, so that $K = 0$ cannot silently trivialize the conclusion. $C$ is existentially quantified
--   ahead of every other object, so no numeral is fixed for it.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 3.1.1, p. 43 (PDF p. 51)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm

open MeasureTheory ProbabilityTheory

namespace HighDimProb.RandomVectors

/-- **Theorem 3.1.1** (Concentration of the norm), Vershynin, *High-Dimensional Probability*
(2018), p. 43.

Let `X = (X₁, …, Xₙ) ∈ ℝⁿ` be a random vector with independent, sub-gaussian coordinates `Xᵢ`
that satisfy `E Xᵢ² = 1`. Then

`‖ ‖X‖₂ − √n ‖_{ψ₂} ≤ C K²`,

where `K = maxᵢ ‖Xᵢ‖_{ψ₂}` and `C` is an absolute constant. -/
theorem concentration_of_the_norm :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X P →
        (∀ i, ∫ ω, (X i ω) ^ 2 ∂P = 1) →
        (∀ i, ∃ t > 0, Integrable (fun ω => Real.exp ((X i ω) ^ 2 / t ^ 2)) P ∧
                       ∫ ω, Real.exp ((X i ω) ^ 2 / t ^ 2) ∂P ≤ 2) →
        HighDimProb.Concentration.subgaussianNorm P
            (fun ω => Real.sqrt (∑ i, (X i ω) ^ 2) - Real.sqrt n) ≤
          C * (⨆ i, HighDimProb.Concentration.subgaussianNorm P (X i)) ^ 2 := by sorry

end HighDimProb.RandomVectors
