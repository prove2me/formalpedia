-- Prove2me | Theorems.Thm_HyperCheeger_lemma_3_3
-- name    : HyperCheeger.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:21.73447+00:00
-- url     : https://prove2.me/theorems/93244dec-0f32-4f10-b663-82b54481be46
-- title:
--   Lemma 3.3 — $H$ and its AE graph have the same matrices
-- statement:
--   For a hypergraph $H$, the AE graph $G_H$ is a 2-graph, and $H$ and $G_H$ have identical adjacency, Laplacian and normalized Laplacian matrices:
--
--   $$A_{G_H}=A_H,\qquad L_{G_H}=L_H,\qquad \mathcal L_{G_H}=\mathcal L_H.$$
--
--   So spectral statements about $G_H$ are spectral statements about $H$.
--
--   Differences from the source:
--   - generalization: we can construct a 2-graph G_H with these matrices → the clauses hold for the explicit aeGraph H; reason: the explicit witness, which is the one the page's proof constructs, implies the existence the lemma states
--   - encoding: the AE graph has parallel edges, or equivalently one edge with the added weight → the merged form, aeGraph, a hypergraph with all hyperedges of size 2; reason: the page offers both forms; the merged one has the same matrices and conductances
--   - encoding: D_H^{-1/2} is undefined with zero degrees → the entry 1/√0 is 0; reason: w_H may vanish; instances with all degrees positive are unchanged
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), Lemma 3.3 and its proof, pp.9–10

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Definitions.Def_HyperCheeger_Hypergraph_aeGraph

namespace HyperCheeger

/-- **Lemma 3.3**: the AE graph `G_H` of `H` is a 2-graph, and `H` and `G_H` have identical adjacency,
Laplacian and normalized Laplacian matrices.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), Lemma 3.3 and its proof, pp.9–10.

**Formalization Note.** The page's "we can construct" is stated for the construction of its proof,
`aeGraph`, which is stronger than a bare existence claim. -/
theorem lemma_3_3 {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) :
    H.aeGraph.IsTwoGraph ∧ H.aeGraph.adj = H.adj ∧ H.aeGraph.lap = H.lap ∧
      H.aeGraph.normLap = H.normLap := by sorry

end HyperCheeger
