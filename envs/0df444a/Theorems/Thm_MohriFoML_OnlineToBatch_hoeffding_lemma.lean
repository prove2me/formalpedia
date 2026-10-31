-- Prove2me | Theorems.Thm_MohriFoML_OnlineToBatch_hoeffding_lemma
-- name    : MohriFoML.OnlineToBatch.hoeffding_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-30T00:08:54.630709+00:00
-- url     : https://prove2.me/theorems/7175a1de-7c6b-4680-b5cf-a8939c681ef8
-- title:
--   Lemma D.1 — Hoeffding's lemma
-- statement:
--   Let $X$ be a real random variable on a probability space with $\mathbb{E}[X] = 0$ and $a \le X \le b$, where $b > a$. Then for every $t > 0$,
--
--   $$
--   \mathbb{E}\big[e^{tX}\big] \le e^{\frac{t^2 (b - a)^2}{8}} .
--   $$
--
--   Hoeffding's lemma bounds the moment generating function of a bounded centred variable by that of a Gaussian with variance $(b-a)^2/4$. Combined with the Chernoff bounding technique (D.1) it yields Hoeffding's inequality (Theorem D.2), which Section 8.4 applies to a fixed near-optimal hypothesis in the proof of (8.28).
--
--   **Formalization Note** $X$ is a measurable function on the probability space and the bounds hold at every point; $X$ and $e^{tX}$ are then integrable, so both expectations are genuine.
--
--   Differences from the source: none.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 437 (PDF p. 454), Appendix D §D.1, Lemma D.1 (Hoeffding's lemma), (D.2)

import Mathlib

namespace MohriFoML.OnlineToBatch

open MeasureTheory

/-- **Lemma D.1: Hoeffding's lemma.**
Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018,
Appendix D, §D.1, p. 437 (PDF p. 454), Lemma D.1, inequality (D.2).

Let `X` be a random variable with `E[X] = 0` and `a ≤ X ≤ b` with `b > a`. Then for any `t > 0`,
`E[e^{tX}] ≤ e^{t²(b−a)²/8}`.

**Formalization Note.** `X` is a measurable real function on a probability space `(Ω, μ)`, and
`a ≤ X ≤ b` holds at every point; together these make `X` and `e^{tX}` integrable, so both
expectations (written as Bochner integrals) are the genuine ones. -/
theorem hoeffding_lemma {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a b : ℝ) (hX : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0) (hab : a < b) (hXab : ∀ ω, a ≤ X ω ∧ X ω ≤ b) :
    ∀ t : ℝ, 0 < t →
      ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by sorry

end MohriFoML.OnlineToBatch
