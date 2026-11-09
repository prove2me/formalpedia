-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_greedy_nested
-- name    : MLAMaxDelay.RandomizedTimer.greedy_nested
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:37:43.045624+00:00
-- url     : https://prove2.me/theorems/ad05d950-16fd-462a-9af4-5dc2c3ab3b7d
-- title:
--   Lemma 4.5 — nested consecutive greedy partitions
-- statement:
--   For a fixed finite input and any $0\le\theta_1\le\theta_2\le1$, every block of the $\theta_2$-greedy partition is a union of consecutive blocks of the $\theta_1$-greedy partition:
--   $$P_{\theta_2}\text{ is a consecutive coarsening of }P_{\theta_1}.$$
--   The claim covers the entire partition, including all suffix blocks, rather than only the first block. Consecutive groups are required to be nonempty and exactly reconstruct the smaller partition.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: one-based closed epoch interval [i,j] → zero-based half-open interval [i-1,j); reason: the same complete epochs and all source index ranges are preserved; empty intervals have equal endpoints
--   - encoding: each larger block is a union of consecutive smaller blocks → an ordered list of nonempty groups flattens to the smaller partition and each group exactly partitions its larger interval; reason: this spells out the same full coarsening relation, including coverage and order
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 12, Lemma 4.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Potential

namespace MLAMaxDelay.RandomizedTimer

/-- Lemma 4.5, p. 12: full consecutive coarsening across the whole input. -/
theorem greedy_nested {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) (θ₁ θ₂ : ℝ)
    (h0 : 0 ≤ θ₁) (h12 : θ₁ ≤ θ₂) (h1 : θ₂ ≤ 1) :
    ConsecutiveCoarsening (greedyPartition T I θ₁) (greedyPartition T I θ₂) := by sorry

end MLAMaxDelay.RandomizedTimer
