-- Prove2me | Theorems.Thm_GenExactSched_lemma_2
-- name    : GenExactSched.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:50.320305+00:00
-- url     : https://prove2.me/theorems/ed9c28c2-8aed-4379-a9ae-6d96f2452bc7
-- title:
--   Lemma 2 — mean and variance of the service capacity $P(t)$ under a rate profile (14)
-- statement:
--   Jobs of types $(\sigma,\tau)$ with law $\mu$ on a bounded set $S\subseteq\{0\le\sigma\le\tau\}$ arrive on $[0,\infty)$ as a Poisson random measure with intensity $\Lambda\,da\otimes\mu$, $\Lambda>0$, and are served by a feasible rate profile $v$ of form (14): a job with remaining time $y$ is served at rate $v(\sigma,\tau,y)\in[0,1]$. Let $P(t)$ be the total service rate at time $t$. Then for every $t\ge0$,
--
--   $$\mathbb E[P(t)]=\Lambda\int\!\!\int_{\tau-t}^{\tau}v(\sigma,\tau,y)\,dy\,d\mu(\sigma,\tau),\qquad \mathrm{Var}(P(t))=\Lambda\int\!\!\int_{\tau-t}^{\tau}v(\sigma,\tau,y)^2\,dy\,d\mu(\sigma,\tau),$$
--
--   and as $t\to\infty$ these converge, so that the stationary moments are
--
--   $$\mathbb E[P]=\Lambda\int\hat\sigma_v(\sigma,\tau)\,d\mu,\qquad \mathrm{Var}(P)=\Lambda\int\!\!\int_{-\infty}^{\tau}v(\sigma,\tau,y)^2\,dy\,d\mu(\sigma,\tau).$$
--
--   This turns the variance of the service capacity into an integral of squared rates, job by job; every optimality result of the paper is a pointwise minimization of this integral plus the penalties.
--
--   Differences from the source:
--   - generalization: ∫_0^τ dy (remaining times in (0, τ]) and the stationary moments only → ∫ over all y ≤ τ (deadline extensions included), and the exact formulas at every finite t ≥ 0 with their t → ∞ limits; reason: under the deadline constraint (3) the range is (0, τ]; Lemma 8, (92) and (97) apply Lemma 2 with extensions (paper.md item 11); the limits are the paper's formulas.
--   - generalization: mark joint density f(σ, τ) on S → any probability measure μ on ℝ² with μ(Sᶜ) = 0; reason: a density is a special case; the statement specializes to the paper's.
--   - encoding: arrival rate Λ without a stated sign → 0 < Λ as a hypothesis; reason: Λ is an arrival rate.
--   - encoding: stationary limit of a process with arrivals on [0, T], with the continuity equation (5) as a constraint → arrivals on [0, ∞); Var(P) is the limsup as t → ∞ of the ℝ≥0∞-valued variance of P(t); (5) is not formalized; reason: (5) only describes the stationary law; Lemma 2 (lemma_2) proves the limit exists, so the limsup is the paper's limit.
--   - encoding: sums Σ_k over jobs, and a rate profile v defined on S × ℝ → integrals against the Poisson random measure N(ω) (Bochner for P(t), lintegral for penalties); v : ℝ → ℝ → ℝ → ℝ jointly measurable on ℝ³, with the extension (σ, τ) ↦ ext_v(σ, τ) measurable; reason: the integral against a counting measure is the sum over its points, a.s. absolutely convergent by Campbell's formula; values of v off {(σ, τ) ∈ S, y ≤ τ} never enter; measurability of ext_v is needed for E[W] to be defined.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Lemma 2, p. 10; proof in Appendix A, p. 38

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure
import Definitions.Def_GenExactSched_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Mean and variance of the service capacity (Lemma 2)**, Nakahira–Ferragut–Wierman,
arXiv:2004.12280v2, Lemma 2, p. 10 (proof in Appendix A, p. 38).

Jobs arrive on `[0, ∞)` as a Poisson random measure `N` with intensity `Λ · da ⊗ μ`, and are served
by a feasible rate profile `v` of form (14). For every `t ≥ 0`,

`E[P(t)] = Λ ∫ ∫_{τ−t}^{τ} v(σ, τ, y) dy dμ`, `Var(P(t)) = Λ ∫ ∫_{τ−t}^{τ} v(σ, τ, y)² dy dμ`,

and as `t → ∞` these tend to `Λ ∫ σ̂_v dμ` and `Λ ∫ ∫_{y ≤ τ} v² dy dμ`; in particular the
stationary variance is `Var(P) = Λ ∫ ∫_{y ≤ τ} v(σ, τ, y)² dy dμ(σ, τ)`.

**Formalization Note.** The paper integrates over `y ∈ (0, τ]`, which is the whole range under
the deadline constraint (3); here `y` ranges over all `y ≤ τ` so that deadline extensions are
covered (the form used in (92) and (97)). The finite-`t` formulas are included. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℝ) (hΛ : 0 < Λ) (S : Set (ℝ × ℝ)) (μ : Measure (ℝ × ℝ)) (hS : MarkAssumptions S μ)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (hN : IsPoissonRandomMeasure P (intensity Λ μ) N)
    (v : ℝ → ℝ → ℝ → ℝ) (hv : Feasible S v) :
    (∀ t : ℝ, 0 ≤ t → ∫ ω, capacity N v t ω ∂P =
      Λ * ∫ q, (∫ y in Set.Icc (q.2 - t) q.2, v q.1 q.2 y) ∂μ) ∧
    (∀ t : ℝ, 0 ≤ t → evariance (capacity N v t) P =
      ENNReal.ofReal (Λ * ∫ q, (∫ y in Set.Icc (q.2 - t) q.2, v q.1 q.2 y ^ 2) ∂μ)) ∧
    Tendsto (fun t : ℝ => ∫ ω, capacity N v t ω ∂P) atTop
      (𝓝 (Λ * ∫ q, σhat v q.1 q.2 ∂μ)) ∧
    Tendsto (fun t : ℝ => evariance (capacity N v t) P) atTop
      (𝓝 (ENNReal.ofReal (Λ * ∫ q, (∫ y in Set.Iic q.2, v q.1 q.2 y ^ 2) ∂μ))) ∧
    statVar P N v = ENNReal.ofReal (Λ * ∫ q, (∫ y in Set.Iic q.2, v q.1 q.2 y ^ 2) ∂μ)
    := by sorry

end GenExactSched
