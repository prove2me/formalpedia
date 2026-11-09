-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_coverage_properties
-- name    : MLAMaxDelay.RandomizedTimer.coverage_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:34.316738+00:00
-- url     : https://prove2.me/theorems/6d75800f-1040-43a7-ae6e-082723bbba70
-- title:
--   Proposition 4.1 — rooted coverage and whole-set diminishing returns
-- statement:
--   For finite sets of labelled occurrences, the rooted coverage cost $\kappa$ is normalized, nonnegative and monotone, as well as subadditive and submodular. Explicitly, for all $A,B$,
--   $$\kappa(A\cup B)+\kappa(A\cap B)\le\kappa(A)+\kappa(B),$$
--   and for every $A\subseteq B$ and every set $Y$,
--   $$\kappa(B\cup Y)-\kappa(B)\le\kappa(A\cup Y)-\kappa(A).$$
--   The singleton diminishing-returns predicate is asserted as well. These are conclusions about the sum of actual covered tree edges, not assumptions about an arbitrary service-cost function.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: submodularity of finite labelled request sets → the published singleton diminishing-returns predicate together with the explicit union/intersection inequality; reason: the theorem supplies both equivalent finite-set forms; the imported predicate bundles no normalization or monotonicity
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 9, Proposition 4.1; proof p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Model
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

namespace MLAMaxDelay.RandomizedTimer

/-- Proposition 4.1, pp. 9–10. All four clauses, including both equivalent
submodularity presentations and whole-set diminishing returns. -/
theorem coverage_properties {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) :
    kappa T I ∅ = 0 ∧ (∀ A, 0 ≤ kappa T I A) ∧
    (∀ A B, A ⊆ B → kappa T I A ≤ kappa T I B) ∧
    (∀ A B, kappa T I (A ∪ B) ≤ kappa T I A + kappa T I B) ∧
    SubsamplingSM.Offline.IsSubmodular (kappa T I) ∧
    (∀ A B, kappa T I (A ∪ B) + kappa T I (A ∩ B) ≤ kappa T I A + kappa T I B) ∧
    (∀ A B Y, A ⊆ B → kappa T I (B ∪ Y) - kappa T I B ≤
      kappa T I (A ∪ Y) - kappa T I A) := by sorry

end MLAMaxDelay.RandomizedTimer
