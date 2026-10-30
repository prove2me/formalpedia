-- Prove2me | Theorems.Thm_GeometricDL_WL_gnn_not_more_powerful_than_wl
-- name    : GeometricDL.WL.gnn_not_more_powerful_than_wl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:24:46.270388+00:00
-- url     : https://prove2.me/theorems/60ad3455-49aa-4d1a-a693-71e0c03c9ae6
-- title:
--   GNNs of the three flavours are no more powerful than the WL test (corrected: convolution coefficients depend on endpoint states and degrees)
-- statement:
--   Let $G_1=(V_1,E_1)$ and $G_2=(V_2,E_2)$ be finite graphs with node features $x^{(1)}:V_1\to F$ and $x^{(2)}:V_2\to F$ in a common feature type $F$. Suppose the Weisfeiler–Lehman test does not distinguish them: at every round $t$ their multisets of WL colours coincide. Then for every local GNN $\mathcal N$ (in particular every stack of convolutional, attentional and message-passing layers (33)–(35)) and every depth $L\ge 0$, the multisets of node states after $L$ layers coincide:
--
--   $$\{\!\{\,h^{(L)}_u(G_1):\ u\in V_1\,\}\!\}=\{\!\{\,h^{(L)}_u(G_2):\ u\in V_2\,\}\!\}.$$
--
--   Consequently every permutation-invariant readout of the final node states (for instance $\varphi\big(\sum_u\psi(h_u)\big)$, eq. (6)) takes the same value on $G_1$ and $G_2$: no GNN of these flavours distinguishes two graphs that the WL test does not distinguish.
--
--   This is the upper bound on the expressive power of GNNs due to Morris et al. (2019) and Xu et al. (2018), as stated in the paper.
--
--   Differences from the source:
--   - correction: convolutional coefficient c_uv "a constant that often directly depends on the entries in A" → c_uv = κ(h_u, h_v, |N_u|, |N_v|), a function of the endpoints' current states and degrees; reason: for G₁ the 6-cycle and G₂ two disjoint triangles, featureless (the paper's own example of graphs WL cannot distinguish), one layer (33) with c_uv = number of triangles of the graph, ψ ≡ 1, ⊕ = Σ, φ(x, z) = z gives h ≡ 0 on G₁ and h ≡ 4 on G₂
--   - generalization: GNNs of the three flavours (33)–(35) → every local GNN, whose layers are arbitrary functions of a node's state and the multiset of (neighbour state, neighbour degree); reason: every flavour layer (with the corrected coefficient) is such a layer (milestone flavours_are_local), so the statement specializes to every stack of flavour layers
--   - generalization: s-dimensional, categorical or featureless node features → features in an arbitrary type F; reason: each of these is a type F
--   - reading: WL "randomly hashing their sums across neighbourhoods" → colour refinement with the canonical injective colour type; reason: a hash with collisions makes the claim false (a constant hash cannot tell a 3-path from a triangle, a GNN summing neighbour degrees can); p. 34 equates one WL step with an injective φ
--   - reading: "cannot be more powerful than the WL test" → WL-indistinguishable graphs (equal colour multisets at every round) get equal multisets of node states from every GNN at every depth; reason: the graph-distinguishing framing of p. 119; equality of the multisets implies equality of every readout
--   - encoding: graph E ⊆ V×V with neighbourhood (11) → a relation E on a finite type, neighbourhood symmetrised, loops allowed, the two graphs on independent node types; reason: Lean convention; same instances
--   - encoding: permutation-invariant aggregator ⊕ → a layer is a function of a multiset; reason: every function of a multiset is permutation-invariant and every permutation-invariant aggregator factors through the multiset
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, Ch. 7, 'The Weisfeiler-Lehman formalism', printed p. 120 (PDF p. 124) ("While the WL test is conceptually simple, and there are many simple examples of non-isomorphic graphs it cannot distinguish, its expressive power is ultimately strongly tied to GNNs. Analyses by Morris et al. (2019) and Xu et al. (2018) have both reached a striking conclusion: any GNN conforming to one of the three flavours we outlined in Section 5.3 cannot be more powerful than the WL test!"); flavours §5.3, eqs. (33)–(35), printed p. 79 (PDF p. 83)

import Mathlib
import Definitions.Def_GeometricDL_WL_WLIndistinguishable
import Definitions.Def_GeometricDL_WL_LocalGNN_state

universe u v

namespace GeometricDL.WL

/-- **GNNs of the three flavours are no more powerful than the Weisfeiler–Lehman test.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, Ch. 7,
'The Weisfeiler-Lehman formalism', printed p. 120 (PDF p. 124): "the WL test is conceptually
simple, and there are many simple examples of non-isomorphic graphs it cannot distinguish, its
expressive power is ultimately strongly tied to GNNs. Analyses by Morris et al. (2019) and Xu et
al. (2018) have both reached a striking conclusion: any GNN conforming to one of the three flavours
we outlined in Section 5.3 cannot be more powerful than the WL test!"; flavours (33)–(35), §5.3,
printed p. 79 (PDF p. 83).

For any two finite node-featured graphs `(V₁, E₁, x₁)` and `(V₂, E₂, x₂)` with features in the
same type `F`: if the WL test does not distinguish them (equal colour multisets at every round),
then for every local GNN `N` and every depth `L` the multisets of node states after `L` layers
coincide. Consequently every readout (any function of that multiset, e.g. (6) `φ(Σ_u ψ(h_u))`)
takes the same value on both graphs.

**Formalization Note.** `LocalGNN` covers every stack of layers of the three flavours (milestone
`flavours_are_local`), with the convolutional coefficient `c_uv = κ(h_u, h_v, |N_u|, |N_v|)`; a
coefficient reading global structure of `A` makes the claim false (6-cycle vs two triangles,
`c_uv` = number of triangles). The WL test uses the canonical injective colour type `WLColor`.
Rounds and layers are 0-based; the graphs may have different node types. -/
theorem gnn_not_more_powerful_than_wl {F : Type u} {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (E₁ : V₁ → V₁ → Prop) [DecidableRel E₁] (x₁ : V₁ → F)
    (E₂ : V₂ → V₂ → Prop) [DecidableRel E₂] (x₂ : V₂ → F)
    (hWL : WLIndistinguishable E₁ x₁ E₂ x₂) (N : LocalGNN.{u, v} F) (L : ℕ) :
    (Finset.univ : Finset V₁).val.map (N.state E₁ x₁ L) =
      (Finset.univ : Finset V₂).val.map (N.state E₂ x₂ L) := by sorry

end GeometricDL.WL
