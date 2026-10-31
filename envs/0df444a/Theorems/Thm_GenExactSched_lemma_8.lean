-- Prove2me | Theorems.Thm_GenExactSched_lemma_8
-- name    : GenExactSched.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:50.25326+00:00
-- url     : https://prove2.me/theorems/37c76732-2e34-4e7d-b0aa-cdc132bccfc1
-- title:
--   Lemma 8 — the profile (89) with deadline extensions solves (88) with value (24)
-- statement:
--   Under the arrival model of the mission, with unit cost $\varepsilon>0$ per unit of deadline extension, consider the feasible rate profiles $v$ of form (14) that meet every demand (constraint (2)), with objective $\mathrm{Var}(P)+E[\varepsilon W]$, where $E[\varepsilon W]$ is the long-run rate of the penalty $\varepsilon(\hat\tau-\tau)_+$; this is problem (88). Then the profile (89),
--
--   $$v(\sigma,\tau,y)=\begin{cases}\dfrac\sigma\tau\,\mathbf 1\{y>0\},&\dfrac\sigma\tau\le\sqrt\varepsilon,\\[1ex] \sqrt\varepsilon\,\mathbf 1\Big\{y>\tau-\dfrac{\sigma}{\sqrt\varepsilon}\Big\},&\text{otherwise},\end{cases}$$
--
--   is optimal with value (24),
--
--   $$\mathrm{Var}(P)+E[\varepsilon W]=\Lambda\,\mathbb E\Big[\frac{\sigma^2}{\tau}\mathbf 1\Big\{\frac\sigma\tau\le\sqrt\varepsilon\Big\}+(2\sqrt\varepsilon\,\sigma-\varepsilon\tau)\,\mathbf 1\Big\{\frac\sigma\tau>\sqrt\varepsilon\Big\}\Big]:$$
--
--   1. (89) is feasible, meets (2), and attains (24);
--   2. every such $v$ costs at least (24);
--   3. every such $v$ attaining (24) equals (89) for $\mu$-a.e. $(\sigma,\tau)$ and a.e. $y\le\tau$.
--
--   This is the core of Theorem 3: under soft deadline constraints a job whose flat rate would exceed $\sqrt\varepsilon$ is served at rate $\sqrt\varepsilon$ past its deadline.
--
--   Differences from the source:
--   - reading: E[W]: expectation of the extension penalty of jobs whose deadline is exactly t → long-run rate lim_{T→∞} (1/T) E[Σ_{k : a_k + τ_k ≤ T} ε(τ̂_k − τ_k)₊] (penaltyRate); reason: at a fixed t the sum is a.s. empty, so E[W(t)] = 0; the E[W] display of p. 40 gives the rate (paper.md item 4).
--   - reading: deadline extension τ̂_k − τ_k with τ̂_k = max{t − a_k : r_k(t) > 0} → (τ̂ − τ)₊ = sup{−y : y ≤ τ, v(σ, τ, y) > 0} in [0, ∞], and 0 if the job is never served after its deadline (ext); reason: taken literally a job finishing early earns a reward and Theorem 3 fails (σ = 1/2, τ = 1, ε = 1); (90) defines this convention (paper.md item 5).
--   - reading: objective written Var(P) + E[W] with ε inside W, and value written for Var(P) + E[εW] → per-job penalty ε·ext, counted once; reason: the value (24) carries a single ε (paper.md item 9).
--   - reading: "the optimal solution" → the profile is optimal, and every optimal feasible profile equals it for μ-a.e. (σ, τ) and Lebesgue-a.e. y ≤ τ; reason: "the" read as uniqueness, the stronger reading; profiles differing on null sets have the same cost, so a.e. is the strongest possible form.
--   - generalization: mark joint density f(σ, τ) on S → any probability measure μ on ℝ² with μ(Sᶜ) = 0; reason: a density is a special case; the statement specializes to the paper's.
--   - encoding: arrival rate Λ and unit cost ε without stated signs → 0 < Λ and 0 < ε as hypotheses; reason: a rate and a unit cost; at ε = 0 the profile (89) serves nothing and violates (2) (paper.md item 7).
--   - encoding: stationary limit of a process with arrivals on [0, T], with the continuity equation (5) as a constraint → arrivals on [0, ∞); Var(P) is the limsup as t → ∞ of the ℝ≥0∞-valued variance of P(t); (5) is not formalized; reason: (5) only describes the stationary law; Lemma 2 (lemma_2) proves the limit exists, so the limsup is the paper's limit.
--   - encoding: sums Σ_k over jobs, and a rate profile v defined on S × ℝ → integrals against the Poisson random measure N(ω) (Bochner for P(t), lintegral for penalties); v : ℝ → ℝ → ℝ → ℝ jointly measurable on ℝ³, with the extension (σ, τ) ↦ ext_v(σ, τ) measurable; reason: the integral against a counting measure is the sum over its points, a.s. absolutely convergent by Campbell's formula; values of v off {(σ, τ) ∈ S, y ≤ τ} never enter; measurability of ext_v is needed for E[W] to be defined.
--   - encoding: σ/τ and σ²/τ for a job with τ = 0 → Lean's x / 0 = 0; reason: on S, τ = 0 forces σ = 0, where the job costs 0 and is served at rate 0; no instance changes.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Lemma 8, p. 40 (problem (88), p. 40; value (24), p. 12); proof pp. 40–41, (90)–(94)

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure
import Definitions.Def_GenExactSched_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Soft deadline constraints: Exact Scheduling with deadline extensions is optimal
(Lemma 8)**, Nakahira–Ferragut–Wierman, arXiv:2004.12280v2, Lemma 8, p. 40, problem (88),
value (24) p. 12.

Over the feasible profiles of form (14) that meet every demand (2), with objective
`Var(P) + E[εW]`, the profile (89),

`v(σ, τ, y) = (σ/τ) 1{y > 0}` if `σ/τ ≤ √ε`, and `√ε 1{y > τ − σ/√ε}` otherwise,

is optimal with value (24), `Λ E[(σ²/τ) 1{σ/τ ≤ √ε} + (2√ε σ − ετ) 1{σ/τ > √ε}]`:

1. (89) is feasible, meets (2), and attains (24);
2. every such `v` costs at least (24);
3. every such `v` attaining (24) equals (89) for `μ`-a.e. `(σ, τ)` and a.e. `y ≤ τ`.

**Formalization Note.** `E[εW]` is the long-run rate `penaltyRate` of the per-job penalty
`ε(τ̂ − τ)₊`, with the extension `ext` of (90) as an `ℝ≥0∞` supremum. -/
theorem lemma_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ ε : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) (S : Set (ℝ × ℝ)) (μ : Measure (ℝ × ℝ))
    (hS : MarkAssumptions S μ)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (hN : IsPoissonRandomMeasure P (intensity Λ μ) N) :
    let v₈ : ℝ → ℝ → ℝ → ℝ := fun σ τ y =>
      if σ / τ ≤ Real.sqrt ε then (if 0 < y then σ / τ else 0)
      else (if τ - σ / Real.sqrt ε < y then Real.sqrt ε else 0)
    let val₂₄ : ℝ := Λ * ∫ q, ((if q.1 / q.2 ≤ Real.sqrt ε then q.1 ^ 2 / q.2 else 0)
      + (if Real.sqrt ε < q.1 / q.2 then 2 * Real.sqrt ε * q.1 - ε * q.2 else 0)) ∂μ
    (Feasible S v₈ ∧ MeetsDemand S v₈ ∧
      statVar P N v₈ + penaltyRate P N (extPenalty ε v₈) = ENNReal.ofReal val₂₄) ∧
    (∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v → MeetsDemand S v →
      ENNReal.ofReal val₂₄ ≤ statVar P N v + penaltyRate P N (extPenalty ε v)) ∧
    (∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v → MeetsDemand S v →
      statVar P N v + penaltyRate P N (extPenalty ε v) = ENNReal.ofReal val₂₄ →
      ∀ᵐ q ∂μ, ∀ᵐ y ∂(volume.restrict (Set.Iic q.2)), v q.1 q.2 y = v₈ q.1 q.2 y) := by sorry

end GenExactSched
