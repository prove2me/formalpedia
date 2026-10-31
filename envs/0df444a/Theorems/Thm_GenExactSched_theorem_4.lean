-- Prove2me | Theorems.Thm_GenExactSched_theorem_4
-- name    : GenExactSched.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:55.644429+00:00
-- url     : https://prove2.me/theorems/54f47777-f757-4108-a132-68a116c1097e
-- title:
--   Theorem 4 — Generalized Exact Scheduling minimizes $\mathrm{Var}(P)+E[\delta U]+E[\varepsilon W]$ (corrected: (25) after deadlines, (26) indicators, uniqueness for $\varepsilon\ne\delta^2/4$)
-- statement:
--   Jobs $(a_k;\sigma_k,\tau_k)$ (arrival time, demand, sojourn time) arrive on $[0,\infty)$ as a Poisson random measure with intensity $\Lambda\,da\otimes\mu(d\sigma,d\tau)$, where $\Lambda>0$ and $\mu$ is a probability law on a bounded set $S\subseteq\{0\le\sigma\le\tau\}$. A unit of unmet demand costs $\delta\ge0$ and a unit of deadline extension costs $\varepsilon>0$. For a feasible rate profile $v$ of form (14), let $\mathrm{cost}(v)=\mathrm{Var}(P)+E[\delta U]+E[\varepsilon W]$ be the stationary variance of the service capacity plus the long-run rates of both penalties (problem (9)). Let $u^*$ be Generalized Exact Scheduling (25) (corrected), $v^*$ the profile (96), and
--
--   $$J^*(\sigma,\tau)=\frac{\sigma^2}{\tau}\mathbf 1\Big\{\frac\sigma\tau\le\min\{\tfrac\delta2,\sqrt\varepsilon\}\Big\}+\delta\Big(\sigma-\frac{\delta\tau}4\Big)\mathbf 1\Big\{\frac\sigma\tau>\frac\delta2,\ \frac\delta2\le\sqrt\varepsilon\Big\}+(2\sqrt\varepsilon\sigma-\varepsilon\tau)\mathbf 1\Big\{\frac\sigma\tau>\sqrt\varepsilon,\ \sqrt\varepsilon<\frac\delta2\Big\}.$$
--
--   Then:
--
--   1. for every job type $(\sigma,\tau)\in S$, the distributed policy $u^*$ of form (4) produces the rates $v^*$ along every trajectory of the remaining demand;
--   2. $v^*$ is feasible and achieves
--   $$\mathrm{Var}(P)+E[\delta U]+E[\varepsilon W]=\Lambda\,\mathbb E\big[J^*(\sigma,\tau)\big];\qquad(26)$$
--   3. every feasible profile of form (14), in particular the realized rates of every policy of form (4), has $\mathrm{cost}(v)\ge\Lambda\,\mathbb E[J^*(\sigma,\tau)]$;
--   4. if $\varepsilon\ne\delta^2/4$, every feasible profile with $\mathrm{cost}(v)=\Lambda\,\mathbb E[J^*(\sigma,\tau)]$ equals $v^*$ for $\mu$-a.e. $(\sigma,\tau)$ and a.e. remaining time $y\le\tau$.
--
--   Generalized Exact Scheduling thus decides, per job and from local information only, whether to meet the demand at a flat rate, to cap the rate at $\delta/2$ and leave demand unmet, or to cap it at $\sqrt\varepsilon$ and extend the deadline; it recovers Exact Scheduling (Theorem 1) and the policies of Theorems 2 and 3 as special cases.
--
--   **Formalization Note** $\mathrm{Var}(P)$ is computed from the point process as the $t\to\infty$ limit of $\mathrm{Var}(P(t))$, and the penalties as long-run rates; neither is defined by a closed form.
--
--   Differences from the source:
--   - correction: policy (25), third line "√ε 1{x > 0} otherwise" → √ε 1{x > 0} only when δ/2 > √ε (and not the first line); rate 0 when δ/2 ≤ √ε and y ≤ 0 (uStar); reason: printed (25) keeps serving past the deadline when δ/2 < √ε: σ = τ = 1, δ = ε = 1 gives cost 5/4, not the claimed optimum 3/4 (paper.md item 1).
--   - correction: (26) with indicators 1{σ/τ > δ/2 ≥ √ε} and 1{σ/τ > √ε > δ/2} → J* with indicators 1{σ/τ > δ/2, δ/2 ≤ √ε} and 1{σ/τ > √ε, √ε < δ/2}; reason: the printed indicators are reversed: at σ = 3/4, τ = 1, δ = 2, ε = 1/4 none fires, so printed (26) is 0 while every policy costs at least 1/2 per job (paper.md item 2).
--   - correction: "the optimal solution" (uniqueness, for all δ, ε) → every optimal feasible profile equals (96) for μ-a.e. (σ, τ) and a.e. y ≤ τ, only when ε ≠ δ²/4; at ε = δ²/4 only optimality is claimed; reason: at ε = δ²/4 uniqueness is false: σ = τ = 1, δ = 1, ε = 1/4, both (δ/2)1{y > 0} and rate 1/2 for two time units cost 3/4 (paper.md item 8).
--   - reading: E[U], E[W]: expectations of penalties of jobs whose deadline is exactly t → long-run rates lim_{T→∞} (1/T) E[Σ_{k : a_k + τ_k ≤ T} penalty_k] (penaltyRate); reason: at a fixed t the sum is a.s. empty, so E[U(t)] = 0 and serving nothing would be free; (81) and the E[W] display (pp. 39–40) give the rate (paper.md item 4).
--   - reading: deadline extension τ̂_k − τ_k with τ̂_k = max{t − a_k : r_k(t) > 0} → (τ̂ − τ)₊ = sup{−y : y ≤ τ, v(σ, τ, y) > 0} in [0, ∞], and 0 if the job is never served after its deadline (ext); reason: taken literally a job finishing early earns a reward and Theorem 3 fails (σ = 1/2, τ = 1, ε = 1); (90) defines this convention (paper.md item 5).
--   - reading: problem (9) without a bound on the service received → feasibility contains σ̂_v(σ, τ) ≤ σ, constraint (80); reason: implied by form (4), where the remaining demand stays ≥ 0, and used by the proofs; without it serving more than the demand lowers the cost (paper.md item 6).
--   - reading: objective written Var(P) + E[U] + E[W] with δ_k, ε_k inside U, W, and value written for Var(P) + E[δU] + E[εW] → per-job penalty δ(σ − σ̂) + ε·ext, each unit cost counted once; reason: the values (22), (24), (26) carry a single δ and ε (paper.md item 9).
--   - encoding: arrival rate Λ and unit costs δ, ε without stated signs → 0 < Λ, 0 ≤ δ, 0 < ε as hypotheses; reason: they are a rate and unit costs; ε > 0 is needed, since at ε = 0 the value (26) is an infimum no policy attains (paper.md item 7).
--   - encoding: stationary limit of a process with arrivals on [0, T], with the continuity equation (5) as a constraint → arrivals on [0, ∞); Var(P) is the limsup as t → ∞ of the ℝ≥0∞-valued variance of P(t); (5) is not formalized; reason: (5) only describes the stationary law; Lemma 2 (lemma_2) proves the limit exists, so the limsup is the paper's limit.
--   - encoding: sums Σ_k over jobs, and a rate profile v defined on S × ℝ → integrals against the Poisson random measure N(ω) (Bochner for P(t), lintegral for penalties); v : ℝ → ℝ → ℝ → ℝ jointly measurable on ℝ³, with the extension (σ, τ) ↦ ext_v(σ, τ) measurable; reason: the integral against a counting measure is the sum over its points, a.s. absolutely convergent by Campbell's formula; values of v off {(σ, τ) ∈ S, y ≤ τ} never enter; measurability of ext_v is needed for E[W] to be defined.
--   - encoding: "scheduler (25) of the form (4) can produce identical service rates to (96)" → a trajectory (continuous, ≥ 0, x(s) = σ − ∫₀ˢ u(x(s'), τ − s') ds') exists, and along every trajectory the rate equals v*(σ, τ, τ − s) for a.e. s ≥ 0 (Produces); reason: the realized rate of a form (4) policy is defined through the remaining-demand trajectory; requiring it along every trajectory rules out a choice of solution.
--   - generalization: minimum over the distributed policies u of form (4) → lower bound over every feasible rate profile v of form (14); reason: the realized rates of every form (4) policy are a profile of form (14) (p. 10, and the paper proves it the same way); it specializes to the paper's claim.
--   - generalization: mark joint density f(σ, τ) on S → any probability measure μ on ℝ² with μ(Sᶜ) = 0; reason: a density is a special case; the statement specializes to the paper's.
--   - encoding: σ/τ and σ²/τ for a job with τ = 0 → Lean's x / 0 = 0; reason: on S, τ = 0 forces σ = 0, where the job costs 0 and is served at rate 0; no instance changes.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Theorem 4, p. 13 (problem (9), p. 8; policy (25) and value (26), p. 13); proof Appendix E, pp. 41–43

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure
import Definitions.Def_GenExactSched_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Generalized Exact Scheduling is optimal (Theorem 4, corrected)**, Nakahira–Ferragut–Wierman,
arXiv:2004.12280v2, Theorem 4, p. 13, problem (9) p. 8, policy (25) and value (26) p. 13.

Let jobs arrive on `[0, ∞)` as a Poisson random measure with intensity `Λ · da ⊗ μ`, `μ` a
probability law of `(σ, τ)` on a bounded set `S ⊆ {0 ≤ σ ≤ τ}`, with unit costs `δ ≥ 0` (unmet
demand) and `ε > 0` (deadline extension). Then

1. for every `(σ, τ) ∈ S`, the corrected policy (25) produces the rates (96);
2. the profile (96) is feasible and `Var(P) + E[δU] + E[εW] = Λ E[J*(σ, τ)]` (corrected (26));
3. every feasible profile of form (14) — in particular the realized rates of every policy of
   form (4) — has `Var(P) + E[δU] + E[εW] ≥ Λ E[J*(σ, τ)]`;
4. if `ε ≠ δ²/4`, every feasible profile attaining `Λ E[J*(σ, τ)]` equals (96) for `μ`-a.e.
   `(σ, τ)` and a.e. remaining time `y ≤ τ`.

**Formalization Note.** `Var(P)` is the `t → ∞` limit of the variance of the capacity built from
the point process (`statVar`); `E[δU]`, `E[εW]` are long-run penalty rates (`penaltyRate`), each
penalty counted once; the extension is `(τ̂ − τ)₊` as in (90); feasibility contains `σ̂ ≤ σ` (80).
The printed (25) and the printed indicators of (26) are false and are corrected (`uStar`,
`Jstar`); "the optimal solution" holds as uniqueness only off the knife edge `ε = δ²/4`. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ δ ε : ℝ) (hΛ : 0 < Λ) (hδ : 0 ≤ δ) (hε : 0 < ε) (S : Set (ℝ × ℝ))
    (μ : Measure (ℝ × ℝ)) (hS : MarkAssumptions S μ)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (hN : IsPoissonRandomMeasure P (intensity Λ μ) N) :
    (∀ q ∈ S, Produces (uStar δ ε) (vStar δ ε) q.1 q.2) ∧
    (Feasible S (vStar δ ε) ∧
      cost δ ε P N (vStar δ ε) = ENNReal.ofReal (optVal Λ δ ε μ)) ∧
    (∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v → ENNReal.ofReal (optVal Λ δ ε μ) ≤ cost δ ε P N v) ∧
    (ε ≠ δ ^ 2 / 4 → ∀ v : ℝ → ℝ → ℝ → ℝ, Feasible S v →
      cost δ ε P N v = ENNReal.ofReal (optVal Λ δ ε μ) →
      ∀ᵐ q ∂μ, ∀ᵐ y ∂(volume.restrict (Set.Iic q.2)), v q.1 q.2 y = vStar δ ε q.1 q.2 y)
    := by sorry

end GenExactSched
