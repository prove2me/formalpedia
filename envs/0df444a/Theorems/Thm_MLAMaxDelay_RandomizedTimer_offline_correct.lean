-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_offline_correct
-- name    : MLAMaxDelay.RandomizedTimer.offline_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:24:18.832983+00:00
-- url     : https://prove2.me/theorems/b649eb48-51bf-48b9-ac72-1ea99ba5a5f0
-- title:
--   Theorem 3.2 — offline value, recovered schedule, and interval recurrence
-- statement:
--   For every input, Algorithm 1 returns the true offline optimum together with a feasible service schedule attaining it. In addition, for every nonempty epoch interval, in source notation,
--   $$D(i,j)=\min_{i\le p\le j}\{D(i,p-1)+C(p,j)+a_j-a_p\}.$$
--   Both output correctness clauses and every subinterval recurrence are retained. This is the exact offline subroutine used to evaluate revealed busy blocks.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: one-based closed epoch interval [i,j] → zero-based half-open interval [i-1,j); reason: the same complete epochs and all source index ranges are preserved; empty intervals have equal endpoints
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
--   - encoding: store any minimizing predecessor and backtrack at the end → choose the smallest minimizing prefix and cache the recovered prefix schedule in each row; reason: this is one permitted tie choice and yields exactly its predecessor-chain schedule; no running-time claim is made
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 6, Theorem 3.2; proof p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Offline

namespace MLAMaxDelay.RandomizedTimer

/-- Theorem 3.2, pp. 6–7: both returned objects and the entire subinterval recurrence. -/
theorem offline_correct {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) :
    (offlineAlgorithm T I).value = optimumReal T I ∧
    ENNReal.ofReal (offlineAlgorithm T I).value = optimum T I ∧
    Feasible T I (offlineAlgorithm T I).schedule ∧
    cost T I (offlineAlgorithm T I).schedule = optimum T I ∧
    (∀ i j : ℕ, i < j → j ≤ (epochs I).length →
      intervalD T I i j = finiteMinimum i j (fun p =>
        intervalD T I i p + intervalC T I p j + epochTime I (j-1) - epochTime I p)) := by sorry

end MLAMaxDelay.RandomizedTimer
