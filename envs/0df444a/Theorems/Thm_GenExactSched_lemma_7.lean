-- Prove2me | Theorems.Thm_GenExactSched_lemma_7
-- name    : GenExactSched.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:58.160804+00:00
-- url     : https://prove2.me/theorems/77d639e0-494c-46de-9b40-91dc838a75c0
-- title:
--   Lemma 7 — the rate-capped profile $\min\{\delta/2,\sigma/\tau\}\mathbf 1\{y>0\}$ solves (77) with value (22)
-- statement:
--   Under the arrival model of the mission, with unit cost $\delta\ge0$ per unit of unmet demand, consider the feasible rate profiles $v$ of form (14) that meet every deadline (constraint (3)), with objective $\mathrm{Var}(P)+E[\delta U]$, where $E[\delta U]$ is the long-run rate of the penalty $\delta(\sigma-\hat\sigma_v)$; this is problem (77). Then the profile (78),
--
--   $$v(\sigma,\tau,y)=\min\Big\{\frac\delta2,\frac\sigma\tau\Big\}\,\mathbf 1\{y>0\},$$
--
--   is optimal with value (22),
--
--   $$\mathrm{Var}(P)+E[\delta U]=\Lambda\,\mathbb E\Big[\frac{\sigma^2}{\tau}\mathbf 1\Big\{\frac\sigma\tau\le\frac\delta2\Big\}+\delta\Big(\sigma-\frac{\delta\tau}{4}\Big)\mathbf 1\Big\{\frac\sigma\tau>\frac\delta2\Big\}\Big]:$$
--
--   1. (78) is feasible, meets (3), and attains (22);
--   2. every such $v$ costs at least (22);
--   3. every such $v$ attaining (22) equals (78) for $\mu$-a.e. $(\sigma,\tau)$ and a.e. $y\le\tau$.
--
--   This is the core of Theorem 2: under soft demand constraints the optimal rate is Exact Scheduling capped at $\delta/2$.
--
--   Differences from the source:
--   - reading: E[U]: expectation of the penalty of jobs whose deadline is exactly t → long-run rate lim_{T→∞} (1/T) E[Σ_{k : a_k + τ_k ≤ T} δ(σ_k − σ̂_k)] (penaltyRate); reason: at a fixed t the sum is a.s. empty, so E[U(t)] = 0 and serving nothing would be free; (81) gives the rate (paper.md item 4).
--   - reading: problem (9) without a bound on the service received → feasibility contains σ̂_v(σ, τ) ≤ σ, constraint (80); reason: implied by form (4), where the remaining demand stays ≥ 0, and used by the proofs; without it serving more than the demand lowers the cost (paper.md item 6).
--   - reading: objective written Var(P) + E[U] with δ inside U, and value written for Var(P) + E[δU] → per-job penalty δ(σ − σ̂), counted once; reason: the value (22) carries a single δ (paper.md item 9).
--   - reading: "the optimal solution" → the profile is optimal, and every optimal feasible profile equals it for μ-a.e. (σ, τ) and Lebesgue-a.e. y ≤ τ; reason: "the" read as uniqueness, the stronger reading; profiles differing on null sets have the same cost, so a.e. is the strongest possible form.
--   - generalization: mark joint density f(σ, τ) on S → any probability measure μ on ℝ² with μ(Sᶜ) = 0; reason: a density is a special case; the statement specializes to the paper's.
--   - encoding: arrival rate Λ and unit cost δ without stated signs → 0 < Λ and 0 ≤ δ as hypotheses; reason: a rate and a unit cost.
--   - encoding: stationary limit of a process with arrivals on [0, T], with the continuity equation (5) as a constraint → arrivals on [0, ∞); Var(P) is the limsup as t → ∞ of the ℝ≥0∞-valued variance of P(t); (5) is not formalized; reason: (5) only describes the stationary law; Lemma 2 (lemma_2) proves the limit exists, so the limsup is the paper's limit.
--   - encoding: sums Σ_k over jobs, and a rate profile v defined on S × ℝ → integrals against the Poisson random measure N(ω) (Bochner for P(t), lintegral for penalties); v : ℝ → ℝ → ℝ → ℝ jointly measurable on ℝ³, with the extension (σ, τ) ↦ ext_v(σ, τ) measurable; reason: the integral against a counting measure is the sum over its points, a.s. absolutely convergent by Campbell's formula; values of v off {(σ, τ) ∈ S, y ≤ τ} never enter; measurability of ext_v is needed for E[W] to be defined.
--   - encoding: σ/τ and σ²/τ for a job with τ = 0 → Lean's x / 0 = 0; reason: on S, τ = 0 forces σ = 0, where the job costs 0 and is served at rate 0; no instance changes.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Lemma 7, p. 39 (problem (77), p. 39; value (22), p. 12); proof pp. 39–40, (79)–(87)

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure
import Definitions.Def_GenExactSched_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Soft demand constraints: the rate-capped Exact Scheduling profile is optimal (Lemma 7)**,
Nakahira–Ferragut–Wierman, arXiv:2004.12280v2, Lemma 7, p. 39, problem (77), value (22) p. 12.

Over the feasible profiles of form (14) that meet every deadline (3), with objective
`Var(P) + E[δU]`, the profile (78), `v(σ, τ, y) = min{δ/2, σ/τ} 1{y > 0}`, is optimal with value (22),

`Λ E[(σ²/τ) 1{σ/τ ≤ δ/2} + δ(σ − δτ/4) 1{σ/τ > δ/2}]`:

1. (78) is feasible, meets (3), and attains (22);
2. every such `v` costs at least (22);
3. every such `v` attaining (22) equals (78) for `μ`-a.e. `(σ, τ)` and a.e. `y ≤ τ`.

**Formalization Note.** `E[δU]` is the long-run rate `penaltyRate` of the per-job penalty
`δ(σ − σ̂_v)`; the penalty is counted once, and `σ̂_v ≤ σ` (80) is part of feasibility. -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ δ : ℝ) (hΛ : 0 < Λ) (hδ : 0 ≤ δ) (S : Set (ℝ × ℝ)) (μ : Measure (ℝ × ℝ))
    (hS : MarkAssumptions S μ)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (hN : IsPoissonRandomMeasure P (intensity Λ μ) N) :
    let v₇ : ℝ → ℝ → ℝ → ℝ := fun σ τ y => if 0 < y then min (δ / 2) (σ / τ) else 0
    let val₂₂ : ℝ := Λ * ∫ q, ((if q.1 / q.2 ≤ δ / 2 then q.1 ^ 2 / q.2 else 0)
      + (if δ / 2 < q.1 / q.2 then δ * (q.1 - δ * q.2 / 4) else 0)) ∂μ
    (Feasible S v₇ ∧ MeetsDeadline S v₇ ∧
      statVar P N v₇ + penaltyRate P N (demandPenalty δ v₇) = ENNReal.ofReal val₂₂) ∧
    (∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v → MeetsDeadline S v →
      ENNReal.ofReal val₂₂ ≤ statVar P N v + penaltyRate P N (demandPenalty δ v)) ∧
    (∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v → MeetsDeadline S v →
      statVar P N v + penaltyRate P N (demandPenalty δ v) = ENNReal.ofReal val₂₂ →
      ∀ᵐ q ∂μ, ∀ᵐ y ∂(volume.restrict (Set.Iic q.2)), v q.1 q.2 y = v₇ q.1 q.2 y) := by sorry

end GenExactSched
