-- Prove2me | Theorems.Thm_MTSActionPredictions_SyncRestart_theorem_6
-- name    : MTSActionPredictions.SyncRestart.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:58:31.953939+00:00
-- url     : https://prove2.me/theorems/c0d4dec3-a325-40cc-a2a0-b078bda90076
-- title:
--   Theorem 6 — synchronized restarts with action predictions
-- statement:
--   Let $(M,d)$ be an arbitrary metric space, fix any collection of allowed tasks $M\to[0,\infty]$, and let $H\ge1$ and $\rho\ge1$. Suppose a causal randomized algorithm with an arbitrary probability law has measurable scalar costs and is strictly $\rho$-competitive on all allowed sequences of at most $H$ requests, uniformly over every restart state and every comparator from that state. For every finite allowed request sequence and deterministic trajectories with $P_0=O_0=x$, the actual Algorithm 1 transformation satisfies
--
--   $$\mathbb E[C_{\rm SyncRestart}]\le(2\rho+1)C(O)+(2\rho+2)\frac{\eta(P,O)}{H}.$$
--
--   The expectation includes one uniform offset independent of the fresh base seeds. No horizon restriction, feasible-prediction condition, positive-comparator-cost assumption, finite-state restriction or additive constant is imposed.
--
--   The same item includes the model's hindsight-comparator scope and Remark 7: predictions may depend on an independent seed with any probability law, and the offline trajectory may depend on those predictions, the offset and every base seed. Whenever the scalar objectives have measurable expectations,
--
--   $$\mathbb E[C_{\rm SyncRestart}]\le(2\rho+1)\mathbb E[C(O)]+(2\rho+2)\frac{\mathbb E[\eta(P,O)]}{H}.$$
--
--   The request list stays fixed. There is no independence assumption on the offline comparator. Fixed predictions with a random hindsight comparator are obtained by taking a one-point prediction seed. This is the full transformation guarantee, with the original deterministic-comparator formula explicitly retained, and is an open proof target.
--
--   Differences from the source:
--   - encoding: nonnegative extended service costs, movement distances, and expectations → ENNReal tasks, metric edist, and nonnegative extended integrals; reason: the same costs and infinities are retained, without conversion to real numbers
--   - encoding: requests indexed from 1 through T and trajectories starting at time 0 → a finite task list with entry i at time i+1 and trajectories on natural times; reason: only the first T+1 states are used, so every finite horizon including zero is represented
--   - encoding: a causal randomized base algorithm initialized at each restart → a seed-indexed rule on a restart state and its revealed task prefix, with scalar measurability on allowed histories; reason: this represents private randomness and defined scalar expectations without imposing topological measurability of tasks or the state space
--   - encoding: a positive block length and uniform random offset, with the base algorithm restarted → H at least 1, a uniform law on Fin H, and an independent finite product of arbitrary base-seed laws; reason: H=0 has no uniform offset; at horizon T at most T+1 seeds suffice, and the seed law need not have finite support
--   - encoding: the displayed deterministic OFF formula, hindsight OFF in §1.1, and independently random predictions in Remark 7 → a conjunction of the original deterministic formula and the formula against fully outcome-dependent OFF with expected cost and error; reason: the expectations make the model convention explicit; independence is imposed only on prediction and algorithm seeds
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; Theorem 6, PDF p. 6 / printed p. 5; Algorithm 1, PDF p. 7 / printed p. 6; proof and Remark 7, PDF pp. 8–9 / printed pp. 7–8

import Definitions.Def_MTSActionPredictions_SyncRestart_Algorithm

open scoped ENNReal BigOperators
open MeasureTheory

namespace MTSActionPredictions.SyncRestart

/-- Theorem 6, PDF 6 / printed 5, Algorithm 1 PDF 7 / printed 6;
proof and Remark 7 PDF 8–9 / printed 7–8. Both the displayed fixed-input
bound and the model's hindsight/random-prediction scope are retained.
The latter has expected OFF and error, and no independence condition on OFF. -/
theorem theorem_6 {Ω M : Type*} [MeasurableSpace Ω] [MetricSpace M]
    (model : Model M) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Rule Ω M) (hA : ScalarMeasurable model A)
    (H : ℕ) (hH : 1 ≤ H) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hcomp : StrictCompetitive model μ A H ρ)
    (x : M) (q : List (Task M)) (hq : ValidTasks model q) :
    (∀ (P O : ℕ → M), P 0 = x → O 0 = x →
      (∫⁻ u, totalCost A x q P H u.1.val u.2 ∂privateLaw μ H q.length) ≤
        ENNReal.ofReal (2 * ρ + 1) * trajectoryCost q O +
        ENNReal.ofReal (2 * ρ + 2) * predictionError q.length P O / (H : ℝ≥0∞)) ∧
    (∀ (Z : Type*) [MeasurableSpace Z] (ν : Measure Z) [IsProbabilityMeasure ν]
      (P : Z → ℕ → M) (hP : ∀ z, P z 0 = x)
      (O : Z × (Fin H × Tape Ω q.length) → ℕ → M)
      (hO : ∀ w, O w 0 = x),
      AEMeasurable (fun w : Z × (Fin H × Tape Ω q.length) =>
        totalCost A x q (P w.1) H w.2.1.val w.2.2) (jointLaw ν μ H q.length) →
      AEMeasurable (fun w => trajectoryCost q (O w)) (jointLaw ν μ H q.length) →
      AEMeasurable (fun w => predictionError q.length (P w.1) (O w))
        (jointLaw ν μ H q.length) →
      (∫⁻ w, totalCost A x q (P w.1) H w.2.1.val w.2.2 ∂jointLaw ν μ H q.length) ≤
        ENNReal.ofReal (2 * ρ + 1) *
          (∫⁻ w, trajectoryCost q (O w) ∂jointLaw ν μ H q.length) +
        ENNReal.ofReal (2 * ρ + 2) *
          (∫⁻ w, predictionError q.length (P w.1) (O w) ∂jointLaw ν μ H q.length) /
          (H : ℝ≥0∞)) := by sorry

end MTSActionPredictions.SyncRestart
