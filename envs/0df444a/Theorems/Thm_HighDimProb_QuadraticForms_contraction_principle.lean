-- Prove2me | Theorems.Thm_HighDimProb_QuadraticForms_contraction_principle
-- name    : HighDimProb.QuadraticForms.contraction_principle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:29:16.685404+00:00
-- url     : https://prove2.me/theorems/d51afd1c-0244-4876-8bcb-bed174b52e44
-- title:
--   Theorem 6.7.1 — Contraction principle
-- statement:
--   This is the **contraction principle**, a comparison inequality for random sums with
--   independent symmetric Bernoulli (Rademacher) coefficients, from Section 6.7 of
--   Vershynin's *High-Dimensional Probability*. It is reused throughout the book's later
--   chaining chapters (Chapters 7 and 8) as a basic tool for bounding expectations of norms
--   of random sums.
--
--   Let $x_1, \dots, x_N$ be deterministic vectors in a normed space, let $a = (a_1, \dots,
--   a_N) \in \mathbb R^N$, and let $\varepsilon_1, \dots, \varepsilon_N$ be independent
--   symmetric Bernoulli random variables (each taking the values $1$ and $-1$ with
--   probability $\tfrac12$). Then
--
--   $$
--   \mathbb E \Bigl\| \sum_{i=1}^N a_i \varepsilon_i x_i \Bigr\|
--   \;\le\; \|a\|_\infty \cdot \mathbb E \Bigl\| \sum_{i=1}^N \varepsilon_i x_i \Bigr\|,
--   \qquad \|a\|_\infty = \max_{1 \le i \le N} |a_i|.
--   $$
--
--   In words: multiplying each term of a Rademacher sum by a bounded coefficient can only
--   increase the expected norm of the sum by a factor of at most the largest coefficient's
--   absolute value.
--
--   **Formalization Note** The normed space is an arbitrary real `NormedAddCommGroup` with a
--   real `NormedSpace` structure, matching the book's "some normed space". The Rademacher
--   hypothesis on $\varepsilon_i$ is stated via the two point-probabilities $P\{\varepsilon_i
--   = 1\} = P\{\varepsilon_i = -1\} = \tfrac12$, the same convention used for Rademacher
--   variables elsewhere in this series (`HighDimProb.Concentration.hoeffding_rademacher`).
--   $\|a\|_\infty$ is written directly as $\sup_i |a_i|$ (`⨆ i, |a i|`) rather than through a
--   library $\ell^\infty$ norm instance, to keep the statement self-contained. Both sides'
--   integrands are assumed `Integrable`, so the inequality is between genuine expectations.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 6.7.1, p. 151 (PDF p. 159)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimProb.QuadraticForms

/-- **Theorem 6.7.1** (Contraction principle), Vershynin, *High-Dimensional Probability*
(2018), p. 151.

Let `x₁, …, x_N` be (deterministic) vectors in some normed space, and let
`a = (a₁, …, a_N) ∈ ℝᴺ`. Then `E ‖∑ᵢ aᵢεᵢxᵢ‖ ≤ ‖a‖_∞ · E ‖∑ᵢ εᵢxᵢ‖`, where `ε₁, …, ε_N` are
independent symmetric Bernoulli (Rademacher) random variables. -/
theorem contraction_principle {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : Fin N → Ω → ℝ) (hε_meas : ∀ i, Measurable (ε i)) (hε_indep : iIndepFun ε P)
    (hε_rad : ∀ i, P.real {ω | ε i ω = 1} = 1 / 2 ∧ P.real {ω | ε i ω = -1} = 1 / 2)
    (x : Fin N → E) (a : Fin N → ℝ)
    (hint1 : Integrable (fun ω => ‖∑ i, (a i * ε i ω) • x i‖) P)
    (hint2 : Integrable (fun ω => ‖∑ i, ε i ω • x i‖) P) :
    ∫ ω, ‖∑ i, (a i * ε i ω) • x i‖ ∂P ≤ (⨆ i, |a i|) * ∫ ω, ‖∑ i, ε i ω • x i‖ ∂P := by sorry

end HighDimProb.QuadraticForms
