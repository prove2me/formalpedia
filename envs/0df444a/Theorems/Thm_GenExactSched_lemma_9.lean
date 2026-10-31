-- Prove2me | Theorems.Thm_GenExactSched_lemma_9
-- name    : GenExactSched.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:59.921913+00:00
-- url     : https://prove2.me/theorems/3fcea74a-99d6-48a7-8521-491f1a533ad1
-- title:
--   Lemma 9 — the profile (96) solves (95) with value (26) (corrected: indicators of (26), uniqueness only for $\varepsilon\ne\delta^2/4$)
-- statement:
--   Under the arrival model of the mission, with unit costs $\delta\ge0$ per unit of unmet demand and $\varepsilon>0$ per unit of deadline extension, consider all feasible rate profiles $v$ of form (14) with objective
--
--   $$\mathrm{cost}(v)=\mathrm{Var}(P)+E[\delta U]+E[\varepsilon W];$$
--
--   this is problem (95). Then:
--
--   1. the profile (96), $v^*$, is feasible and $\mathrm{cost}(v^*)=\Lambda\,\mathbb E[J^*(\sigma,\tau)]$, the corrected value (26);
--   2. every feasible $v$ has $\mathrm{cost}(v)\ge\Lambda\,\mathbb E[J^*(\sigma,\tau)]$;
--   3. if $\varepsilon\ne\delta^2/4$, every feasible $v$ with $\mathrm{cost}(v)=\Lambda\,\mathbb E[J^*(\sigma,\tau)]$ equals (96) for $\mu$-a.e. $(\sigma,\tau)$ and a.e. $y\le\tau$.
--
--   Here $J^*(\sigma,\tau)=\frac{\sigma^2}{\tau}$ when $\sigma/\tau\le\min\{\delta/2,\sqrt\varepsilon\}$, $\delta(\sigma-\delta\tau/4)$ when $\sigma/\tau>\delta/2$ and $\delta/2\le\sqrt\varepsilon$, and $2\sqrt\varepsilon\,\sigma-\varepsilon\tau$ when $\sigma/\tau>\sqrt\varepsilon$ and $\sqrt\varepsilon<\delta/2$. This is the lower bound that Theorem 4 transfers to the distributed policy (25).
--
--   Differences from the source:
--   - correction: (26) with indicators 1{σ/τ > δ/2 ≥ √ε} and 1{σ/τ > √ε > δ/2} → J* with indicators 1{σ/τ > δ/2, δ/2 ≤ √ε} and 1{σ/τ > √ε, √ε < δ/2}; reason: the printed indicators are reversed: at σ = 3/4, τ = 1, δ = 2, ε = 1/4 none fires, so printed (26) is 0 while every policy costs at least 1/2 per job (paper.md item 2).
--   - correction: "the optimal solution" (uniqueness, for all δ, ε) → every optimal feasible profile equals (96) for μ-a.e. (σ, τ) and a.e. y ≤ τ, only when ε ≠ δ²/4; at ε = δ²/4 only optimality is claimed; reason: at ε = δ²/4 uniqueness is false: σ = τ = 1, δ = 1, ε = 1/4, both (δ/2)1{y > 0} and rate 1/2 for two time units cost 3/4 (paper.md item 8).
--   - reading: E[U], E[W]: expectations of penalties of jobs whose deadline is exactly t → long-run rates lim_{T→∞} (1/T) E[Σ_{k : a_k + τ_k ≤ T} penalty_k] (penaltyRate); reason: at a fixed t the sum is a.s. empty, so E[U(t)] = 0 and serving nothing would be free; (81) and the E[W] display (pp. 39–40) give the rate (paper.md item 4).
--   - reading: deadline extension τ̂_k − τ_k with τ̂_k = max{t − a_k : r_k(t) > 0} → (τ̂ − τ)₊ = sup{−y : y ≤ τ, v(σ, τ, y) > 0} in [0, ∞], and 0 if the job is never served after its deadline (ext); reason: taken literally a job finishing early earns a reward and Theorem 3 fails (σ = 1/2, τ = 1, ε = 1); (90) defines this convention (paper.md item 5).
--   - reading: problem (9) without a bound on the service received → feasibility contains σ̂_v(σ, τ) ≤ σ, constraint (80); reason: implied by form (4), where the remaining demand stays ≥ 0, and used by the proofs; without it serving more than the demand lowers the cost (paper.md item 6).
--   - reading: objective written Var(P) + E[U] + E[W] with δ_k, ε_k inside U, W, and value written for Var(P) + E[δU] + E[εW] → per-job penalty δ(σ − σ̂) + ε·ext, each unit cost counted once; reason: the values (22), (24), (26) carry a single δ and ε (paper.md item 9).
--   - generalization: mark joint density f(σ, τ) on S → any probability measure μ on ℝ² with μ(Sᶜ) = 0; reason: a density is a special case; the statement specializes to the paper's.
--   - encoding: arrival rate Λ and unit costs δ, ε without stated signs → 0 < Λ, 0 ≤ δ, 0 < ε as hypotheses; reason: they are a rate and unit costs; ε > 0 is needed, since at ε = 0 the value (26) is an infimum no policy attains (paper.md item 7).
--   - encoding: stationary limit of a process with arrivals on [0, T], with the continuity equation (5) as a constraint → arrivals on [0, ∞); Var(P) is the limsup as t → ∞ of the ℝ≥0∞-valued variance of P(t); (5) is not formalized; reason: (5) only describes the stationary law; Lemma 2 (lemma_2) proves the limit exists, so the limsup is the paper's limit.
--   - encoding: sums Σ_k over jobs, and a rate profile v defined on S × ℝ → integrals against the Poisson random measure N(ω) (Bochner for P(t), lintegral for penalties); v : ℝ → ℝ → ℝ → ℝ jointly measurable on ℝ³, with the extension (σ, τ) ↦ ext_v(σ, τ) measurable; reason: the integral against a counting measure is the sum over its points, a.s. absolutely convergent by Campbell's formula; values of v off {(σ, τ) ∈ S, y ≤ τ} never enter; measurability of ext_v is needed for E[W] to be defined.
--   - encoding: σ/τ and σ²/τ for a job with τ = 0 → Lean's x / 0 = 0; reason: on S, τ = 0 forces σ = 0, where the job costs 0 and is served at rate 0; no instance changes.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Lemma 9, p. 41 (problem (95), p. 41; value (26), p. 13); proof pp. 41–42, (97)–(104)

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure
import Definitions.Def_GenExactSched_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Soft demand and deadline constraints: the profile (96) is optimal (Lemma 9, value
corrected)**, Nakahira–Ferragut–Wierman, arXiv:2004.12280v2, Lemma 9, p. 41, problem (95), value
(26) p. 13.

Over all feasible profiles of form (14), with objective `Var(P) + E[δU] + E[εW]` (`cost`):

1. the profile (96), `vStar`, is feasible and its cost is `Λ E[J*(σ, τ)]` (`optVal`, the corrected
   (26));
2. every feasible `v` costs at least `Λ E[J*(σ, τ)]`;
3. if `ε ≠ δ²/4`, every feasible `v` attaining `Λ E[J*(σ, τ)]` equals (96) for `μ`-a.e. `(σ, τ)`
   and a.e. `y ≤ τ`.

**Formalization Note.** The value uses the corrected indicators of (26) (`Jstar`). Uniqueness
fails at `ε = δ²/4`, where `(δ/2) 1{y > 0}` and an extended flat rate can tie. -/
theorem lemma_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ δ ε : ℝ) (hΛ : 0 < Λ) (hδ : 0 ≤ δ) (hε : 0 < ε) (S : Set (ℝ × ℝ))
    (μ : Measure (ℝ × ℝ)) (hS : MarkAssumptions S μ)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (hN : IsPoissonRandomMeasure P (intensity Λ μ) N) :
    (Feasible S (vStar δ ε) ∧
      cost δ ε P N (vStar δ ε) = ENNReal.ofReal (optVal Λ δ ε μ)) ∧
    (∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v → ENNReal.ofReal (optVal Λ δ ε μ) ≤ cost δ ε P N v) ∧
    (ε ≠ δ ^ 2 / 4 → ∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v →
      cost δ ε P N v = ENNReal.ofReal (optVal Λ δ ε μ) →
      ∀ᵐ q ∂μ, ∀ᵐ y ∂(volume.restrict (Set.Iic q.2)), v q.1 q.2 y = vStar δ ε q.1 q.2 y)
    := by sorry

end GenExactSched
