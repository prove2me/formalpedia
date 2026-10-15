-- Prove2me | Theorems.Thm_LNChannels_RateBounds_lemma_1
-- name    : LNChannels.RateBounds.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:27.510878+00:00
-- url     : https://prove2.me/theorems/bd9707a2-9a47-4ada-b069-e43102d7e10e
-- title:
--   Lemma 1, p. 6 — the on-chain cost of a Poisson transaction stream with rate $\lambda$ is $C\lambda/r$
-- statement:
--   Let $\xi_0,\xi_1,\xi_2,\dots$ be independent random variables on a probability space, each exponentially distributed with rate $\lambda>0$; they are the interarrival times of a Poisson process with rate $\lambda$, whose arrival times are
--   $$\tau_n=\xi_0+\xi_1+\dots+\xi_{n-1},\qquad n\ge1.$$
--   Each arrival is a payment settled on chain at the fixed cost $C$, and costs are discounted at the rate $r>0$. Then the expected discounted on-chain cost is finite and equals
--   $$\mathbb E\Big[\sum_{n\ge1} e^{-r\tau_n}\,C\Big]=\frac{C\lambda}{r}.$$
--
--   This is the benchmark against which the paper measures every payment channel: a channel is worthwhile only if its cost is below $C\lambda/r$ (and below $2C\lambda/r$ for two streams of rate $\lambda$).
--
--   **Formalization Note** The Poisson process is represented by its i.i.d. exponential interarrival times, through the published definition `QueueingFundamentals.Foundations.IsExpInterarrivals` (measurable, mutually independent, each with law `expMeasure λ`), with `arrivalTime ξ n` $=\xi_0+\dots+\xi_{n-1}$; this is the description the proof itself uses ("the interarrival times … are independent"). The conclusion asserts integrability of the discounted sum as well as the value of its integral, so Lean's convention that a non-integrable function has integral $0$ cannot make the statement easier.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 6 (PDF p. 7), Lemma 1; proof pp. 9–10 (PDF pp. 10–11)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace LNChannels.RateBounds

/-- Lemma 1 (On-chain Cost), p. 6: a stream of transactions arriving at the jumps of a Poisson
process with rate `lam` (i.i.d. exponential interarrival times `ξ 0, ξ 1, …`, arrival times
`τₙ = ξ 0 + ⋯ + ξ (n−1)`, `n ≥ 1`), each settled on chain at cost `C`, has expected discounted cost
`E[∑_{n ≥ 1} e^{−r τₙ} C] = C λ / r`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (lam r C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (ξ : ℕ → Ω → ℝ)
    (hξ : IsExpInterarrivals μ lam ξ) :
    Integrable (fun ω => ∑' n : ℕ, Real.exp (-r * arrivalTime ξ (n + 1) ω) * C) μ ∧
      ∫ ω, ∑' n : ℕ, Real.exp (-r * arrivalTime ξ (n + 1) ω) * C ∂μ = C * lam / r := by sorry

end LNChannels.RateBounds
