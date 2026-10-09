-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_lemma_1
-- name    : GreedWorks.OnlineList.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:36.705244+00:00
-- url     : https://prove2.me/theorems/de493828-511a-4b74-b5f3-bd44207f39d3
-- title:
--   Lemma 1, p. 5 — integer-valued tail-sum identities
-- statement:
--   Let $X$ be a measurable nonnegative integer-valued random variable on a probability space. Its first and second moments satisfy the tail identities
--
--   $$\sum_{r\ge0}\mathbb P(X>r)=\mathbb E[X],\qquad\sum_{r\ge0}\left(r+\frac12\right)\mathbb P(X>r)=\frac12\mathbb E[X^2].$$
--
--   These identities convert processing-time tails into the coefficients of the time-indexed relaxation. **Formalization Note** Both equalities are in the extended nonnegative reals, so they also cover infinite moments without a default value for a divergent real series.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 5, Lemma 1

import Mathlib

namespace GreedWorks.OnlineList

open MeasureTheory

/-- Gupta et al., Lemma 1, p. 5: the two tail-sum identities for a nonnegative
integer-valued random variable.  Extended nonnegative values include infinite moments. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : Ω → ℕ) (hX : Measurable X) :
    (∑' r : ℕ, Pr {ω | r < X ω}) = (∫⁻ ω, (X ω : ENNReal) ∂Pr) ∧
    (∑' r : ℕ, ((r : ENNReal) + 1 / 2) * Pr {ω | r < X ω}) =
      (1 / 2 : ENNReal) * (∫⁻ ω, ((X ω : ENNReal) ^ 2) ∂Pr) := by sorry

end GreedWorks.OnlineList
