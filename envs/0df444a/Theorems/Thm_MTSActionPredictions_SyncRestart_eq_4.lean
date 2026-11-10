-- Prove2me | Theorems.Thm_MTSActionPredictions_SyncRestart_eq_4
-- name    : MTSActionPredictions.SyncRestart.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:58:37.608384+00:00
-- url     : https://prove2.me/theorems/2e2b54fb-7f53-40f1-aa1e-5c9e8208a4c6
-- title:
--   Section 3, equation (4) — expected running cost at a fixed offset
-- statement:
--   Fix any metric state space, allowed extended-cost tasks, an initial state $x$, a finite request sequence of length $T$, and deterministic predictions and comparator trajectories with $P_0=O_0=x$. Let $H\ge1$, $\rho\ge1$, and let the causal randomized rule be strictly $\rho$-competitive on every valid input of at most $H$ tasks from every restart state. Its scalar costs have defined measurable expectations. Fix $s\in\{0,\ldots,H-1\}$. For the actual Algorithm 1 run with this offset, let $C_{\rm Alg}$ omit synchronization moves and put $E_s=\sum_{1\le t\le T,\ t\bmod H=s}d(P_t,O_t)$. Then
--
--   $$\mathbb E[C_{\rm Alg}\mid s]\le\rho(C(O)+E_s).$$
--
--   The expectation is over the independent base seeds alone. Partial first and last blocks and a synchronization at the terminal request are included. The estimate controls actual block-service costs from the short-input hypothesis, rather than assuming a scalar cost bound.
--
--   Differences from the source:
--   - encoding: nonnegative extended service costs, movement distances, and expectations → ENNReal tasks, metric edist, and nonnegative extended integrals; reason: the same costs and infinities are retained, without conversion to real numbers
--   - encoding: requests indexed from 1 through T and trajectories starting at time 0 → a finite task list with entry i at time i+1 and trajectories on natural times; reason: only the first T+1 states are used, so every finite horizon including zero is represented
--   - encoding: a causal randomized base algorithm initialized at each restart → a seed-indexed rule on a restart state and its revealed task prefix, with scalar measurability on allowed histories; reason: this represents private randomness and defined scalar expectations without imposing topological measurability of tasks or the state space
--   - encoding: a positive block length and uniform random offset, with the base algorithm restarted → H at least 1, a uniform law on Fin H, and an independent finite product of arbitrary base-seed laws; reason: H=0 has no uniform offset; at horizon T at most T+1 seeds suffice, and the seed law need not have finite support
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; §3, equation (4), PDF p. 8 / printed p. 7

import Definitions.Def_MTSActionPredictions_SyncRestart_Algorithm

open scoped ENNReal BigOperators
open MeasureTheory

namespace MTSActionPredictions.SyncRestart

/-- Section 3, (4), PDF 8 / printed 7: fixed offset, all finite horizons,
including partial first/last blocks. The strict hypothesis is on the base rule. -/
theorem eq_4 {Ω M : Type*} [MeasurableSpace Ω] [MetricSpace M]
    (model : Model M) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Rule Ω M) (hA : ScalarMeasurable model A)
    (H : ℕ) (hH : 1 ≤ H) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hcomp : StrictCompetitive model μ A H ρ)
    (x : M) (q : List (Task M)) (hq : ValidTasks model q)
    (P O : ℕ → M) (hP : P 0 = x) (hO : O 0 = x) (s : Fin H) :
    (∫⁻ ω, runningCost A x q P H s.val ω ∂tapeLaw μ q.length) ≤
      ENNReal.ofReal ρ * (trajectoryCost q O + syncError q.length H s.val P O) := by sorry

end MTSActionPredictions.SyncRestart
