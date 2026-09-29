-- Prove2me | Theorems.Thm_OnlinePrimalDual_Routing_routing_competitive
-- name    : OnlinePrimalDual.Routing.routing_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:49:57.057492+00:00
-- url     : https://prove2.me/theorems/ba439727-b550-4cba-8acd-4b0332fab032
-- title:
--   Theorem 9.2 — the routing algorithm is (1, O(log n))-competitive (goal)
-- statement:
--   Composing Lemma 9.1's per-copy bandwidth and load guarantees across all graph copies, via
--   the book's own backward-induction accounting (bundled as an explicit hypothesis) and
--   edge-multiplicity argument (bundled as an explicit hypothesis): the algorithm's total accepted
--   bandwidth is at least the offline-optimal splittable bandwidth M (the "1" of the bicriterion,
--   exact, no loss), and the global load on any edge is O(log n) (the second factor).
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 204, Theorem 9.2

import Mathlib

namespace OnlinePrimalDual.Routing

/-- **Theorem 9.2** (p. 204, PDF p. 115) — the goal of this mission: the generic routing
algorithm is `(1, O(log n))`-competitive with respect to all splittable routing solutions.

Composes Lemma 9.1's per-copy guarantee across the `J`-indexed family of graph copies
`G₀,…,Gₖ` (Section 9.1's construction, just before Lemma 9.1). `Mcopy j` is copy `j`'s share
`|Mⱼ|` of the offline-optimal splittable solution's bandwidth (the book's own grouping of the
optimal solution's paths by bottleneck-capacity range, p. 204); `accepted j` is the bandwidth the
algorithm actually routes in copy `j`. `hper_copy_bandwidth` is Lemma 9.1's part (i), applied at
every copy. `hquota` packages the book's own backward-induction argument (p. 204-205, "We prove
by backward induction that the total bandwidth allocated by the algorithm in levels `Gⱼ` to `Gₖ`
is at least `|Mⱼ|+|Mⱼ₊₁|+⋯+|Mₖ|`... the total bandwidth ... in levels `G₀` to `Gₖ` is at least
`M`") as a single hypothesis, `M ≤ ∑ⱼ Mcopyⱼ`, rather than re-deriving the induction's own
combinatorial grouping-by-bottleneck-capacity construction; given this and `hper_copy_bandwidth`,
`M ≤ ∑ⱼ acceptedⱼ` follows by termwise comparison and transitivity — the "`1`" (exact, no loss)
half of the bicriterion.

`hper_copy_load` is Lemma 9.1's part (ii), applied uniformly (every copy shares the same `n`).
`hload_aggregation` packages the book's own edge-multiplicity argument (p. 205, "the total
capacity of the copies of edge `e` in all levels is at most four times its capacity... the total
number of requests routed on edge `e` in all levels is at most `O(log n)` times the sum of the
capacities of `e` in all levels") as a single hypothesis relating the global load (across all
copies combined, on any edge) to the uniform per-copy load bound via the `≤4×`-multiplicity
factor, rather than re-deriving the specific geometric decay of `u(e,j) = min(u(e), mʲ⁺²)` across
levels. The conclusion's load bound `8+24log₂n` is `4·(2+6log₂n)` (Lemma 9.1's own bound, scaled
by the `4`-copy multiplicity), the "`O(log n)`" half of the bicriterion. -/
theorem routing_competitive {J : Type*} [Fintype J]
    (Mcopy accepted : J → ℝ) (M loadPerCopy globalLoad n : ℝ)
    (hper_copy_bandwidth : ∀ j, Mcopy j ≤ accepted j)
    (hquota : M ≤ ∑ j, Mcopy j)
    (hn_pos : 0 < n)
    (hper_copy_load : loadPerCopy ≤ 2 + 6 * Real.logb 2 n)
    (hload_aggregation : globalLoad ≤ 4 * loadPerCopy) :
    M ≤ ∑ j, accepted j ∧ globalLoad ≤ 8 + 24 * Real.logb 2 n := by sorry

end OnlinePrimalDual.Routing
