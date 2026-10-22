-- Prove2me | Theorems.Thm_GeomDL_Sets_complete_graph_aggregate_constant
-- name    : GeomDL.Sets.complete_graph_aggregate_constant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:20.715587+00:00
-- url     : https://prove2.me/theorems/1da38464-7c72-456a-8b17-34ae8579ab9f
-- title:
--   §5.4, p. 81 — on the complete graph A = 𝟙𝟙ᵀ the aggregate ⊕ᵥ ψ(xᵥ) is the same for all nodes u
-- statement:
--   Consider the convolutional-type layer $\mathbf h_u=\phi\big(\mathbf x_u,\bigoplus_{v\in\mathcal N_u}\psi(\mathbf x_v)\big)$, where $\psi:\mathbb R^d\to M$ and the permutation-invariant aggregator $\bigoplus$ acts on the multiset $\{\!\{\psi(\mathbf x_v):v\in\mathcal N_u\}\!\}$ with values in $M'$. On the complete graph $\mathbf A=\mathbf 1\mathbf 1^\top$, every neighbourhood is $\mathcal V$, so for any input $\mathbf X$ and nodes $u,w$,
--
--   $$\bigoplus_{v\in\mathcal N_u}\psi(\mathbf x_v)=\bigoplus_{v\in\mathcal N_w}\psi(\mathbf x_v).$$
--
--   Thus the layer receives the same aggregate as its second input at every node, as stated in §5.4, p. 81.
--
--   **Formalization Note** This item covers the page's constant-aggregate clause. Its subsequent claim that the complete-graph layer has the same expressive power as a node-only layer fails across inputs: with two nodes and sum aggregation, changing only the second node can change the first node's output.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.4, Complete edge set, p. 81 and side-note

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

namespace GeomDL.Sets

/-- §5.4, p. 81 (and side-note): on the complete graph `A = 𝟙𝟙ᵀ` (so `N_u = V`),
the permutation-invariant aggregate `⊕_{v ∈ V} ψ(x_v)` supplied as the second input to
`h_u = φ(x_u, ⊕_{v ∈ V} ψ(x_v))` is identical at every node `u`. -/
theorem complete_graph_aggregate_constant {n d : ℕ} {M M' : Type*}
    (ψ : (Fin d → ℝ) → M) (agg : Multiset M → M')
    (X : Matrix (Fin n) (Fin d) ℝ) :
    ∀ u w : Fin n,
      agg ((neighbourhood (allOnes n) u).val.map (fun v => ψ (X v))) =
        agg ((neighbourhood (allOnes n) w).val.map (fun v => ψ (X v))) := by sorry

end GeomDL.Sets
