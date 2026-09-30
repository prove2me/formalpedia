-- Prove2me | Theorems.Thm_NonuniformCompetitive_SpinBlock_expected_wait_cost
-- name    : NonuniformCompetitive.SpinBlock.expected_wait_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:51:45.218984+00:00
-- url     : https://prove2.me/theorems/2a46b01c-4e23-4fe5-93ae-0a0f79212f9f
-- title:
--   §4.1, p. 560 — expected cost of a lock wait: $\pi(\tau)C+\int_0^\tau(1-\pi(t))\,dt$
-- statement:
--   Let $C>0$ be the context-switch cost, and let the blocking time $b\in[0,\infty]$ of an algorithm be random with law $\nu$, a probability measure on $[0,\infty]$. Write $\pi(t)=\nu\{b<t\}$ for the probability that the algorithm blocks before time $t$. For a lock released at time $\tau\ge0$, the expected cost of the wait is
--   $$\mathbf{E}\,\mathrm{waitCost}_C(b,\tau)=\pi(\tau)\cdot C+\int_0^\tau\big(1-\pi(t)\big)\,dt ,$$
--   where $1-\pi(t)=\nu\{b\ge t\}$ is the probability that the process is still spinning at time $t$. The first term is the expected cost of blocking and the second the expected cost of spinning.
--
--   The identity reduces the competitive analysis of a randomized spin-block algorithm on a single lock wait to a one-dimensional computation with its distribution function; the paper applies it to its particular distribution $\pi$.
--
--   **Formalization Note** The identity is stated for every blocking law $\nu$, not only the paper's $\pi$, exactly as the paper's explanation of its two terms applies. Both sides are in $[0,\infty]$; the integral is a lower Lebesgue integral over $(0,\tau]$, so no integrability hypothesis is needed. The convention that a tie $b=\tau$ costs $\tau$ is what makes $\pi(\tau)=\nu\{b<\tau\}$ (strict) and $1-\pi(t)=\nu\{b\ge t\}$ the right sets.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 560, §4.1, proof of Theorem 10, display for E C_A(σ_τ)

import Mathlib
import Definitions.Def_NonuniformCompetitive_SpinBlock_Model

open scoped NNReal ENNReal
open MeasureTheory

namespace NonuniformCompetitive.SpinBlock

/-- §4.1, p. 560, the expected-cost display: if the blocking time `b` of an algorithm has law `ν`
(a probability measure on `[0, ∞]`) and the lock is released at time `τ`, the expected cost is
`π(τ) · C + ∫₀^τ (1 − π(t)) dt`, where `π(τ) = ν{b < τ}` is the probability of blocking before `τ`
and `1 − π(t) = ν{b ≥ t}` is the probability of still spinning at time `t`. -/
theorem expected_wait_cost (C : ℝ) (hC : 0 < C) (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    (τ : ℝ≥0) :
    ∫⁻ b, waitCost C b τ ∂ν =
      ν (Set.Iio (τ : ℝ≥0∞)) * ENNReal.ofReal C +
        ∫⁻ t in Set.Ioc (0 : ℝ) τ, ν (Set.Ici (ENNReal.ofReal t)) := by sorry

end NonuniformCompetitive.SpinBlock
