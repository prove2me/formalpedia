-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_lemma_5_10
-- name    : NonMarkovColorings.Main.lemma_5_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:08:42.652094+00:00
-- url     : https://prove2.me/theorems/671aa3a7-0aa1-4439-87fd-e69bab6092db
-- title:
--   Lemma 5.10 — an exponential variable on an event of probability $p$: $\mathbb E[X\mathbf 1\{A\}]\le p(\mu\log(e/p)+1)$
-- statement:
--   Let $X$ be an exponential random variable with mean $\mu>0$ and let $A$ be an event of probability $p$. Then
--   $$\mathbb E[X\mathbf 1\{A\}]\le p\,\big(\mu\log(e/p)+1\big).$$
--   It converts high-probability bounds into expectation bounds in §5.2.
--
--   **Formalization Note.** $X$ is measurable with law `expMeasure (1/μ)` (rate $1/\mu$); $A$ is a measurable set and $p=$ `P.real A`; at $p=0$ both sides are $0$ under Lean's conventions ($\log 0=0$).
--
--   Differences from the source:
--   - encoding: exponential random variable with mean μ, event A → Measurable X, P.map X = expMeasure (1/μ), MeasurableSet A; E[X1{A}] = ∫ A.indicator X ∂P; reason: the law fixes integrability of X, so the Bochner integral is the expectation
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 36, Lemma 5.10

import Mathlib

namespace NonMarkovColorings.Main

/-- Lemma 5.10 ([HV03, Observation 21]). If `X` is an exponential random variable with mean
`μ` and `A` is an event of probability `p`, then `E[X 1{A}] ≤ p (μ log(e/p) + 1)`. -/
theorem lemma_5_10 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (μ : ℝ) (hμ : 0 < μ) (X : Ω → ℝ)
    (hX : Measurable X) (hlaw : P.map X = ProbabilityTheory.expMeasure (1 / μ))
    (A : Set Ω) (hA : MeasurableSet A) :
    ∫ ω, A.indicator X ω ∂P ≤
      P.real A * (μ * Real.log (Real.exp 1 / P.real A) + 1) := by sorry

end NonMarkovColorings.Main
