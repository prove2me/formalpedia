-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_partition_optimum
-- name    : MLAMaxDelay.RandomizedTimer.partition_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:29.777791+00:00
-- url     : https://prove2.me/theorems/1ff58cd6-42c2-4740-86e7-5b5bf0397342
-- title:
--   Proposition 3.1 — partition and schedule optima
-- statement:
--   For every finite labelled input $I$ on the weighted rooted tree, let $\operatorname{OPT}(I)$ minimize actual feasible schedule cost and let $\Phi^\star(I)$ minimize total ideal batch cost over arbitrary request partitions. Then
--   $$\operatorname{OPT}(I)=\Phi^\star(I).$$
--   The offline value is finite and attained by a feasible schedule, including the empty schedule for the empty input. This identifies the arbitrary-batch partition objective with actual rooted services, rather than defining one from the other.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
--   - encoding: minimum cost of a feasible offline schedule → explicit finite attained minimum alongside the equality; reason: the source calls this a minimum and constructs an attaining schedule in the proposition proof
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 6, Proposition 3.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Model

namespace MLAMaxDelay.RandomizedTimer

/-- Proposition 3.1, p. 6. Equality with arbitrary-batch partition optimization;
the minimum is attained by an actual feasible schedule and is finite. -/
theorem partition_optimum {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) :
    optimum T I = partitionOptimum T I ∧ optimum T I ≠ ⊤ ∧
      ∃ S : Schedule V, Feasible T I S ∧ cost T I S = optimum T I := by sorry

end MLAMaxDelay.RandomizedTimer
