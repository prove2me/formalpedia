-- Prove2me | Theorems.Thm_MTSActionPredictions_SyncRestart_eq_5
-- name    : MTSActionPredictions.SyncRestart.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:58:34.597893+00:00
-- url     : https://prove2.me/theorems/c4bf2d71-6916-4f4f-955d-5b45f11c7c78
-- title:
--   Section 3, equation (5) — pathwise synchronization cost
-- statement:
--   Fix any metric state space, a finite sequence of nonnegative extended-cost tasks, predictions and an offline trajectory with $P_0=O_0=x$, an integer $H\ge1$, and an offset $s\in\{0,\ldots,H-1\}$. For every causal base rule and every realized seed tape, the operational run of Algorithm 1 satisfies
--
--   $$C_{\rm sync}\le C_{\rm Alg}+C(O)+2\sum_{1\le t\le T,\ t\bmod H=s}d(P_t,O_t).$$
--
--   Here $C_{\rm Alg}$ includes all within-block movement and service, while $C_{\rm sync}$ includes only extra moves after serving boundary requests. This is a pathwise estimate; it needs neither competitiveness nor a probability distribution on tapes. It applies also to infeasible predictions, infinite service costs, zero requests and partial boundary blocks. It supplies the second supporting estimate for Theorem 6.
--
--   Differences from the source:
--   - encoding: nonnegative extended service costs, movement distances, and expectations → ENNReal tasks, metric edist, and nonnegative extended integrals; reason: the same costs and infinities are retained, without conversion to real numbers
--   - encoding: requests indexed from 1 through T and trajectories starting at time 0 → a finite task list with entry i at time i+1 and trajectories on natural times; reason: only the first T+1 states are used, so every finite horizon including zero is represented
--   - generalization: equation (5) within the proof for a strictly competitive randomized base algorithm → the same pathwise estimate for every causal rule and arbitrary seed tape, without competitiveness or a probability law; reason: the metric argument uses neither hypothesis, and every source run is an instance of the quantified rule and tape
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; §3, equation (5), PDF p. 8 / printed p. 7

import Definitions.Def_MTSActionPredictions_SyncRestart_Algorithm

open scoped ENNReal BigOperators
open MeasureTheory

namespace MTSActionPredictions.SyncRestart

/-- Section 3, (5), PDF 8 / printed 7: a pathwise metric estimate, with
no competitiveness or probability assumption. -/
theorem eq_5 {Ω M : Type*} [MetricSpace M]
    (A : Rule Ω M) (tape : ℕ → Ω) (H : ℕ) (hH : 1 ≤ H)
    (x : M) (q : List (Task M)) (P O : ℕ → M)
    (hP : P 0 = x) (hO : O 0 = x) (s : Fin H) :
    (run A tape x q P H s.val q.length).costSync ≤
      (run A tape x q P H s.val q.length).costAlg + trajectoryCost q O +
        2 * syncError q.length H s.val P O := by sorry

end MTSActionPredictions.SyncRestart
