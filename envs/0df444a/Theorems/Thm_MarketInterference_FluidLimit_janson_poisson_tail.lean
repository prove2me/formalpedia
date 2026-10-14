-- Prove2me | Theorems.Thm_MarketInterference_FluidLimit_janson_poisson_tail
-- name    : MarketInterference.FluidLimit.janson_poisson_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:53.442992+00:00
-- url     : https://prove2.me/theorems/9a6ed663-7ee6-4156-8461-5aaea9a8051f
-- title:
--   Proof of Lemma 2, p. 38 — Poisson tail P(V ≥ t) ≤ exp(−t) for t ≥ 7λ₀ (Janson–Łuczak–Ruciński, Cor. 2.4)
-- statement:
--   Let $V$ be a Poisson random variable with mean $\lambda_0\ge 0$. Then for every $t\ge 7\lambda_0$,
--
--   $$
--   \mathbb P(V\ge t)\le e^{-t}.
--   $$
--
--   The bound is quoted in the proof of Lemma 2 from Janson, Łuczak and Ruciński (*Random Graphs*, 2000, Corollary 2.4). It is the tail estimate that makes the supremum of the scaled Poisson counts integrable.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 38, proof of Lemma 2 (citing Janson, Łuczak and Ruciński 2000, Corollary 2.4)

import Mathlib

namespace MarketInterference.FluidLimit

open MeasureTheory ProbabilityTheory NNReal

/-- The Poisson tail bound quoted in the proof of Lemma 2 (arXiv:2205.02274v4, p. 38; Janson, Łuczak
and Ruciński 2000, Corollary 2.4): if `V ∼ Poisson(λ₀)` then `P(V ≥ t) ≤ exp(-t)` for all `t ≥ 7 λ₀`. -/
theorem janson_poisson_tail (l0 : ℝ≥0) (t : ℝ) (ht : 7 * (l0 : ℝ) ≤ t) :
    (poissonMeasure l0).real {n : ℕ | t ≤ (n : ℝ)} ≤ Real.exp (-t) := by sorry

end MarketInterference.FluidLimit
