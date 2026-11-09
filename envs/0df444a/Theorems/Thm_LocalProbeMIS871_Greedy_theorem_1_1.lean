-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_theorem_1_1
-- name    : LocalProbeMIS871.Greedy.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:53:08.021358+00:00
-- url     : https://prove2.me/theorems/fe13bae4-ed6b-4259-8788-bd8e5ec5cf32
-- title:
--   Theorem 1.1 — Simultaneous degree-six probe bound for randomized greedy MIS
-- statement:
--   Let $r$ be the original vector of independent uniforms on $(0,1)$, with law $\mu_n$. The query algorithm uses caching and early stopping within each query, reads the degree and complete neighbor list of a fresh vertex, and breaks rank ties by labels. Its greedy set $I_G(r)$ and cost $Q_G(v,r)$ are computed from that execution.
--
--   There is an absolute $C>0$ such that for every $n$, every finite simple labeled graph $G$ on $n$ vertices, every integer degree bound $\Delta\ge2$, every fixed adjacency-list ordering, and every $0<\delta<1$, with probability at least $1-\delta$ all answers are membership indicators of the same greedy maximal independent set and
--
--   $$\forall v\in V(G),\qquad Q_G(v,r)\le C\Delta^6\left(1+\ln\frac n\delta\right).$$
--
--   For $n=0$ there are no queries; the success event is certain. Every query is a terminating recursion on its lexicographic key.
--
--   The event is simultaneous for all vertices under one shared rank assignment; each root receives a fresh cache. No algorithmic correctness or tail certificate is assumed.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: O(Δ^6(1+ln(n/δ))) probes simultaneously, answering membership in the greedy MIS → one existential positive C before all inputs and an event combining the uniform bound, greedy membership, independence, and domination; reason: this expands big-O and the membership-query semantics of §2 without changing their strength; n=0 is handled before the logarithm
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 2, PDF p. 4, Theorem 1.1 and §2 correctness; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Theorem 1.1, printed p.2 / PDF4, with §2 correctness made explicit.
The n=0 branch has no queries and avoids log(0). Every run terminates by rank recursion. -/
theorem theorem_1_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (n Δ : ℕ), 2 ≤ Δ → ∀ G : SimpleGraph (Fin n), (∀ u, G.degree u ≤ Δ) →
    ∀ lists : AdjacencyLists G, ∀ δ : ℝ, 0 < δ → δ < 1 →
      ENNReal.ofReal (1 - δ) ≤ rankLaw n {r |
        (∀ v, (execution G r v).1 = decide (v ∈ I G r)) ∧
        (∀ u ∈ I G r, ∀ z ∈ I G r, ¬ G.Adj u z) ∧
        (∀ u, u ∉ I G r → ∃ z ∈ I G r, G.Adj u z) ∧
        (if n = 0 then True else ∀ v,
          (Q G lists v r : ℝ) ≤ C * (Δ : ℝ) ^ (6 : ℕ) * (1 + Real.log ((n : ℝ) / δ)))} := by sorry

end LocalProbeMIS871.Greedy
