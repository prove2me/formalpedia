-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_potential_endpoints
-- name    : MLAMaxDelay.RandomizedTimer.potential_endpoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:38.721876+00:00
-- url     : https://prove2.me/theorems/0c3ac06b-7dc1-4d1a-9124-8630bbea3a06
-- title:
--   Lemma 5.2 — existence and bounds at both parameter endpoints
-- statement:
--   Fix a nonempty input (the timer potential $Q$ is computed on its zero-path preprocessing). Both endpoint limits exist as finite real numbers and satisfy
--   $$0\le Q(0^+),\qquad Q(1^-)\le\operatorname{OPT}(I).$$
--   The statement uses the right limit at zero and the left limit at one, not $Q(0)$ and $Q(1)$. The comparison is with the actual offline schedule optimum of the original input.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
--   - encoding: fixed nonempty input, with Q on the partitions of the preprocessed epochs → nonempty original input, Q computed on the positive reduction and OPT on the original input; reason: preprocessing is the algorithm's cost-free step; the original offline benchmark is retained, not replaced by a positivity assumption on all requests
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 14, Lemma 5.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Potential

namespace MLAMaxDelay.RandomizedTimer

/-- Lemma 5.2, p. 14. Existence of both limits is part of the conclusion. -/
theorem potential_endpoints {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) (hI : I.requests.Nonempty) :
    ∃ qzero qone : ℝ, HasRightPotentialLimit T I 0 qzero ∧
      HasLeftPotentialLimit T I 1 qone ∧ 0 ≤ qzero ∧ qone ≤ optimumReal T I := by sorry

end MLAMaxDelay.RandomizedTimer
