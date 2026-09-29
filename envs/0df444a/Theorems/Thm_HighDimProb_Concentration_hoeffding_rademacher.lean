-- Prove2me | Theorems.Thm_HighDimProb_Concentration_hoeffding_rademacher
-- name    : HighDimProb.Concentration.hoeffding_rademacher
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:35:48.677104+00:00
-- url     : https://prove2.me/theorems/5691357e-4a21-4bbd-93ad-b7d98391c44e
-- title:
--   Theorem 2.2.2 — Hoeffding's inequality
-- statement:
--   This is **Hoeffding's inequality** for a weighted sum of independent Rademacher
--   (symmetric Bernoulli) random variables.
--
--   Let $(\Omega, \mathcal F, P)$ be a probability space, let $X_1, \dots, X_N : \Omega \to
--   \mathbb R$ be independent random variables each taking the values $-1$ and $1$ with
--   probability $\tfrac12$ each (the symmetric Bernoulli, or Rademacher, distribution), and
--   let $a = (a_1, \dots, a_N) \in \mathbb R^N$. Then, for every $t \ge 0$,
--
--   $$
--   P\Bigl\{\sum_{i=1}^N a_i X_i \ge t\Bigr\} \;\le\; \exp\!\left(-\frac{t^2}{2\|a\|_2^2}\right),
--   $$
--
--   where $\|a\|_2^2 = \sum_{i=1}^N a_i^2$.
--
--   This is the simplest non-trivial concentration inequality: it gives an exponentially
--   small, one-sided tail bound for a weighted coin-flip sum, matching (with the
--   normalization $\|a\|_2 = 1$) exactly the tail of the standard normal distribution — a
--   quantitative, non-asymptotic form of the central limit theorem that holds for every fixed
--   $N$, not only in the limit.
--
--   **Formalization Note** $\Omega$, its $\sigma$-algebra, and $P$ are an explicit probability
--   space, with `P.real` Mathlib's $\mathbb R$-valued measure evaluation. The Rademacher
--   hypothesis is stated directly via the two point-probabilities
--   $P\{X_i = 1\} = P\{X_i = -1\} = \tfrac12$, which forces $X_i \in \{-1, 1\}$ almost surely.
--   This is the one-sided form of the book's Theorem 2.2.2 (the two-sided form with $|\cdot|$
--   is Theorem 2.2.5, a routine corollary not separately included in this mission).
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 2.2.2, p. 16 (PDF p. 24)

import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace HighDimProb.Concentration

/-- **Theorem 2.2.2** (Hoeffding's inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 16.

Let `X₁, …, X_N` be independent symmetric Bernoulli (Rademacher) random variables, and
`a = (a₁, …, a_N) ∈ ℝᴺ`. Then, for any `t ≥ 0`,

`P {∑ᵢ aᵢXᵢ ≥ t} ≤ exp(−t² / (2‖a‖₂²))`. -/
theorem hoeffding_rademacher {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_rad : ∀ i, P.real {ω | X i ω = 1} = 1 / 2 ∧ P.real {ω | X i ω = -1} = 1 / 2)
    (a : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ ∑ i, a i * X i ω} ≤ Real.exp (-(t ^ 2 / (2 * ∑ i, (a i) ^ 2))) := by sorry

end HighDimProb.Concentration
