-- Prove2me | Theorems.Thm_GenExactSched_lemma_1
-- name    : GenExactSched.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:56.450572+00:00
-- url     : https://prove2.me/theorems/5550df72-b906-4663-a400-f470017fed8d
-- title:
--   Lemma 1 — Exact Scheduling $(\sigma/\tau)\mathbf 1\{y>0\}$ minimizes $\mathrm{Var}(P)$ under strict demand and deadline constraints
-- statement:
--   Under the arrival model of the mission, consider the feasible rate profiles $v$ of form (14) that meet every demand, $\int_{-\infty}^{\tau}v(\sigma,\tau,y)\,dy=\sigma$ (constraint (2)), and every deadline, $v(\sigma,\tau,y)=0$ for $y\le0$ (constraint (3)); this is problem (15). Then the profile (16),
--
--   $$v(\sigma,\tau,y)=\frac{\sigma}{\tau}\,\mathbf 1\{y>0\},$$
--
--   is optimal:
--
--   1. it is feasible, meets (2) and (3), and its stationary capacity variance is $\mathrm{Var}(P)=\Lambda\,\mathbb E[\sigma^2/\tau]$;
--   2. every such $v$ has $\mathrm{Var}(P)\ge\Lambda\,\mathbb E[\sigma^2/\tau]$;
--   3. every such $v$ with $\mathrm{Var}(P)=\Lambda\,\mathbb E[\sigma^2/\tau]$ equals (16) for $\mu$-a.e. $(\sigma,\tau)$ and a.e. $y\le\tau$.
--
--   This is the core of Theorem 1: serving every job at the flat rate $\sigma/\tau$ until its deadline minimizes the fluctuation of the service capacity.
--
--   Differences from the source:
--   - reading: "the optimal solution" → the profile is optimal, and every optimal feasible profile equals it for μ-a.e. (σ, τ) and Lebesgue-a.e. y ≤ τ; reason: "the" read as uniqueness, the stronger reading; profiles differing on null sets have the same cost, so a.e. is the strongest possible form.
--   - generalization: mark joint density f(σ, τ) on S → any probability measure μ on ℝ² with μ(Sᶜ) = 0; reason: a density is a special case; the statement specializes to the paper's.
--   - encoding: arrival rate Λ without a stated sign → 0 < Λ as a hypothesis; reason: Λ is an arrival rate.
--   - encoding: stationary limit of a process with arrivals on [0, T], with the continuity equation (5) as a constraint → arrivals on [0, ∞); Var(P) is the limsup as t → ∞ of the ℝ≥0∞-valued variance of P(t); (5) is not formalized; reason: (5) only describes the stationary law; Lemma 2 (lemma_2) proves the limit exists, so the limsup is the paper's limit.
--   - encoding: sums Σ_k over jobs, and a rate profile v defined on S × ℝ → integrals against the Poisson random measure N(ω) (Bochner for P(t), lintegral for penalties); v : ℝ → ℝ → ℝ → ℝ jointly measurable on ℝ³, with the extension (σ, τ) ↦ ext_v(σ, τ) measurable; reason: the integral against a counting measure is the sum over its points, a.s. absolutely convergent by Campbell's formula; values of v off {(σ, τ) ∈ S, y ≤ τ} never enter; measurability of ext_v is needed for E[W] to be defined.
--   - encoding: σ/τ and σ²/τ for a job with τ = 0 → Lean's x / 0 = 0; reason: on S, τ = 0 forces σ = 0, where the job costs 0 and is served at rate 0; no instance changes.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Lemma 1, p. 10 (problem (15), p. 10); proof p. 11, (17)–(20)

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure
import Definitions.Def_GenExactSched_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Exact Scheduling minimizes the stationary variance under strict constraints (Lemma 1)**,
Nakahira–Ferragut–Wierman, arXiv:2004.12280v2, Lemma 1, p. 10, problem (15).

Over the feasible profiles of form (14) that meet every demand (2) and every deadline (3), the
profile (16), `v(σ, τ, y) = (σ/τ) 1{y > 0}`, is optimal:

1. (16) is feasible, meets (2) and (3), and has `Var(P) = Λ E[σ²/τ]`;
2. every such `v` has `Var(P) ≥ Λ E[σ²/τ]`;
3. every such `v` attaining `Λ E[σ²/τ]` equals (16) for `μ`-a.e. `(σ, τ)` and a.e. `y ≤ τ`.

**Formalization Note.** `Var(P)` is `statVar`, the `t → ∞` limit of the variance of the capacity
built from the point process. Uniqueness is read from "the optimal solution". -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℝ) (hΛ : 0 < Λ) (S : Set (ℝ × ℝ)) (μ : Measure (ℝ × ℝ)) (hS : MarkAssumptions S μ)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (hN : IsPoissonRandomMeasure P (intensity Λ μ) N) :
    let v₁ : ℝ → ℝ → ℝ → ℝ := fun σ τ y => if 0 < y then σ / τ else 0
    (Feasible S v₁ ∧ MeetsDemand S v₁ ∧ MeetsDeadline S v₁ ∧
      statVar P N v₁ = ENNReal.ofReal (Λ * ∫ q, q.1 ^ 2 / q.2 ∂μ)) ∧
    (∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v → MeetsDemand S v → MeetsDeadline S v →
      ENNReal.ofReal (Λ * ∫ q, q.1 ^ 2 / q.2 ∂μ) ≤ statVar P N v) ∧
    (∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v → MeetsDemand S v → MeetsDeadline S v →
      statVar P N v = ENNReal.ofReal (Λ * ∫ q, q.1 ^ 2 / q.2 ∂μ) →
      ∀ᵐ q ∂μ, ∀ᵐ y ∂(volume.restrict (Set.Iic q.2)), v q.1 q.2 y = v₁ q.1 q.2 y) := by sorry

end GenExactSched
