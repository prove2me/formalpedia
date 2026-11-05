-- Prove2me | Theorems.Thm_OmniThreshold_lemma_1
-- name    : OmniThreshold.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:38.833284+00:00
-- url     : https://prove2.me/theorems/c5692a39-d562-4c93-80a3-da3f77c2787b
-- title:
--   Lemma 1 — the min-cost flow value is supermodular in the source supplies
-- statement:
--   Consider a finite network with arbitrary real arc costs and integer arc capacities. It has distinct source nodes $\mathrm{src}(k)$, $k\in\iota$, and a sink $t$ that is not a source. For integer supplies $b\in\mathbb N^\iota$ at the sources, let $V(b)\in\mathbb R\cup\{+\infty\}$ be the minimum cost of a feasible flow when the sink absorbs the total supply $\sum_kb_k$. Then $V$ is **supermodular**: for all $b,b'\in\mathbb N^\iota$,
--   $$
--   V(b)+V(b')\le V(b\vee b')+V(b\wedge b'),
--   $$
--   where $\vee$ and $\wedge$ are the coordinatewise maximum and minimum.
--
--   Applied to the bipartite fulfillment network, this lemma gives the paper's monotonicity of marginal fulfillment costs.
--
--   **Formalization Note** $V(b)=+\infty$ when $b$ admits no feasible flow, so the inequality is stated for all supply vectors. Flows are real.
--
--   Differences from the source:
--   - reading: one sink with integer demand → the sink's demand is the total supply $\sum_kb_k$ and all other non-source nodes conserve flow; reason: with one sink and supplies that vary, the problem is balanced only when the sink absorbs the total supply, as in Appendix B and in the network of p.10 ("The sink node has demand equal to the sum of the supplies")
--   - generalization: the objective value of a minimum cost feasible flow → a value in $\mathbb R\cup\{+\infty\}$ (`WithTop ℝ`), $+\infty$ for infeasible supplies; reason: the source speaks only of feasible problems. On supplies where all four values are finite the inequality is the source's; where a value is $+\infty$ the statement adds that $b$ and $b'$ are feasible whenever $b\vee b'$ and $b\wedge b'$ both are
--   - encoding: integer supplies and capacities at "multiple sources" and "one sink" → natural-number supplies and capacities, distinct source nodes (`src` injective) and a sink that is not a source, real flows and arbitrary real arc costs; reason: supplies and capacities of a flow problem are nonnegative, the sources and the sink are different nodes, and the source puts no condition on costs; with integer data a real and an integer optimum coincide
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, Lemma 1, p.9; proof in Appendix B, p.28

import Mathlib
import Definitions.Def_OmniThreshold_FlowNetwork
import Definitions.Def_OmniThreshold_minCostFlowValue

namespace OmniThreshold

/-- **Lemma 1** (Jia, Karp, Ravi & Tayur, *Effective Online Order Acceptance Policies for
Omni-Channel Fulfillment*, SSRN 3932692, Lemma 1, p.9; proof in Appendix B, p.28): "In a
minimum-cost, single-commodity flow problem with multiple sources, one sink, and integer supplies,
demands, and capacities, the objective value of a minimum cost feasible flow as a function of the
supplies at the source nodes is supermodular."

For a finite network `G` with integer capacities and arbitrary real arc costs, distinct source
nodes `src k` and a sink `t` that is not a source, the optimal value `V(b)` of the min-cost flow
with supplies `b` (and sink demand `∑ b`) satisfies
`V(b) + V(b') ≤ V(b ⊔ b') + V(b ⊓ b')` for all integer supply vectors `b, b'`.

**Formalization Note** `V` takes values in `WithTop ℝ`, with `⊤` for an infeasible supply vector,
so the inequality is stated for all supply vectors without feasibility hypotheses. Supplies are
natural numbers; flows are real (`minCostFlowValue`). -/
theorem lemma_1 {V E ι : Type*} [Fintype V] [Fintype E] [Fintype ι] [DecidableEq V]
    (G : FlowNetwork V E) (src : ι ↪ V) (t : V) (ht : t ∉ Set.range src) (b b' : ι → ℕ) :
    minCostFlowValue G src t b + minCostFlowValue G src t b' ≤
      minCostFlowValue G src t (b ⊔ b') + minCostFlowValue G src t (b ⊓ b') := by sorry

end OmniThreshold
