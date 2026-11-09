-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_interval_bounds
-- name    : MLAMaxDelay.RandomizedTimer.interval_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:24:10.409025+00:00
-- url     : https://prove2.me/theorems/627d1e8c-84d9-46a0-8fc0-431ea3562620
-- title:
--   Lemma 4.2 — both interval optimum bounds
-- statement:
--   For every finite input with distinct arrival epochs $a_1<\cdots<a_n$ and every $1\le i\le j\le n$, the true offline subinstance optimum obeys
--   $$C(i,j)\le D(i,j)\le C(i,j)+a_j-a_i.$$
--   Both inequalities compare actual rooted schedule costs with the joint rooted footprint. They apply to zero spatial costs and single-epoch intervals too.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: one-based closed epoch interval [i,j] → zero-based half-open interval [i-1,j); reason: the same complete epochs and all source index ranges are preserved; empty intervals have equal endpoints
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 10, Lemma 4.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Offline

namespace MLAMaxDelay.RandomizedTimer

/-- Lemma 4.2, p. 10; both bounds, every nonempty epoch interval. -/
theorem interval_bounds {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) (i j : ℕ)
    (hij : i < j) (hjn : j ≤ (epochs I).length) :
    intervalC T I i j ≤ intervalD T I i j ∧
      intervalD T I i j ≤ intervalC T I i j + epochTime I (j-1) - epochTime I i := by sorry

end MLAMaxDelay.RandomizedTimer
