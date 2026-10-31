-- Prove2me | Theorems.Thm_GenExactSched_eq_81
-- name    : GenExactSched.eq_81
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:03.349811+00:00
-- url     : https://prove2.me/theorems/64d12ad2-a387-48c9-9f48-4beb8746b3be
-- title:
--   (81) and the $E[W]$ display — long-run penalty rates equal $\Lambda$ times the mean per-job penalty
-- statement:
--   Under the arrival model of the mission ($\Lambda>0$, job types with law $\mu$ on a bounded $S\subseteq\{0\le\sigma\le\tau\}$, Poisson arrivals on $[0,\infty)$), let $c(\sigma,\tau)\in[0,\infty]$ be any measurable per-job penalty. Then
--
--   $$\lim_{T\to\infty}\frac1T\,\mathbb E\Big[\sum_{k:\ a_k+\tau_k\le T}c(\sigma_k,\tau_k)\Big]=\Lambda\int c\,d\mu,$$
--
--   the value $+\infty$ included. In particular, with $c=\sigma-\hat\sigma(\sigma,\tau)$ the long-run rate of unmet demand is $E[U]=\int(\sigma-\hat\sigma(\sigma,\tau))\,\Lambda f(\sigma,\tau)\,d\sigma\,d\tau$, eq. (81), and with $c=(\hat\tau-\tau)_+$ the long-run rate of deadline extension is $E[W]=\int(\hat\tau(\sigma,\tau)-\tau)\,\Lambda f(\sigma,\tau)\,d\sigma\,d\tau$ (p. 40).
--
--   These identities turn the two penalties of problem (9) into per-job integrals, so that the objective becomes a single integral over job types.
--
--   Differences from the source:
--   - reading: E[U], E[W]: expectations of penalties of jobs whose deadline is exactly t → long-run rates lim_{T→∞} (1/T) E[Σ_{k : a_k + τ_k ≤ T} penalty_k] (penaltyRate); reason: at a fixed t the sum is a.s. empty, so E[U(t)] = 0 and serving nothing would be free; (81) and the E[W] display (pp. 39–40) give the rate (paper.md item 4).
--   - generalization: the two penalties σ − σ̂(σ, τ) and τ̂(σ, τ) − τ → every measurable per-job penalty c : ℝ² → [0, ∞], value ∞ included; reason: c = δ(σ − σ̂_v) and c = ε(τ̂ − τ)₊ are instances, so it specializes to (81) and to the E[W] display.
--   - generalization: mark joint density f(σ, τ) on S → any probability measure μ on ℝ² with μ(Sᶜ) = 0; reason: a density is a special case; the statement specializes to the paper's.
--   - encoding: arrival rate Λ without a stated sign → 0 < Λ as a hypothesis; reason: Λ is an arrival rate.
--   - encoding: arrivals on [0, T] and a stationary limit; sums over jobs → arrivals on [0, ∞); expectations of integrals against N(ω); the rate is also shown to equal penaltyRate (a limsup); reason: the same long-run rate; the integral against the counting measure is the sum over jobs.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Appendix C, (79)–(81), p. 39, and Appendix D, the E[W] display, p. 40

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure
import Definitions.Def_GenExactSched_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Long-run penalty rates (81) and the mean of W**, Nakahira–Ferragut–Wierman,
arXiv:2004.12280v2, Appendix C, (81), p. 39, and Appendix D, p. 40.

For every measurable per-job penalty `c(σ, τ) ∈ [0, ∞]`, the expected total penalty of the jobs
whose deadline `a + τ` lies in `[0, T]`, divided by `T`, converges as `T → ∞` to `Λ ∫ c dμ`
(possibly `∞`); so the long-run penalty rate is `Λ ∫ c dμ`. With `c = σ − σ̂` this is (81),
`E[U] = ∫ (σ − σ̂(σ, τ)) Λ f(σ, τ) dσ dτ`, and with `c = (τ̂ − τ)₊` it is the display
`E[W] = ∫ (τ̂(σ, τ) − τ) Λ f(σ, τ) dσ dτ` of p. 40.

**Formalization Note.** `E[U]` and `E[W]` are read as long-run rates: the paper's `U(t)` sums over
jobs with deadline exactly `t`, which is almost surely empty at a fixed `t`. -/
theorem eq_81 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℝ) (hΛ : 0 < Λ) (S : Set (ℝ × ℝ)) (μ : Measure (ℝ × ℝ)) (hS : MarkAssumptions S μ)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (hN : IsPoissonRandomMeasure P (intensity Λ μ) N)
    (c : ℝ × ℝ → ℝ≥0∞) (hc : Measurable c) :
    Tendsto (fun T : ℝ => (ENNReal.ofReal T)⁻¹ *
        ∫⁻ ω, ∫⁻ p, Set.indicator {p : ℝ × (ℝ × ℝ) | p.1 + p.2.2 ≤ T} (fun p => c p.2) p
          ∂(N ω) ∂P) atTop
      (𝓝 (ENNReal.ofReal Λ * ∫⁻ q, c q ∂μ)) ∧
    penaltyRate P N c = ENNReal.ofReal Λ * ∫⁻ q, c q ∂μ := by sorry

end GenExactSched
