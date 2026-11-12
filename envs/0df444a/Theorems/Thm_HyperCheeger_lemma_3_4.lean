-- Prove2me | Theorems.Thm_HyperCheeger_lemma_3_4
-- name    : HyperCheeger.lemma_3_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:04:43.894022+00:00
-- url     : https://prove2.me/theorems/0b95397f-2642-49ea-9254-37816579eba9
-- title:
--   Lemma 3.4 — $\phi_g(T)=\hat\phi_h(T)$ on the AE graph
-- statement:
--   Let $H$ be a hypergraph, $G_H$ its AE graph, and $\emptyset\subsetneq T\subsetneq V_H$. Then
--
--   $$\phi_g(T)=\hat\phi_h(T),$$
--
--   where the left side is the conductance of $T$ in $G_H$ and the right side is the diffusion conductance of $T$ in $H$. This is the key property of the AE graph: its cuts measure diffusion conductance.
--
--   Differences from the source:
--   - encoding: the conductance of a set is undefined when a side has volume 0 → the quotient 0/0 is 0; reason: w_H may vanish; a zero denominator has a zero numerator, and sets with both volumes positive are unchanged
--   - encoding: the AE graph has parallel edges, or equivalently one edge with the added weight → the merged form, aeGraph, a hypergraph with all hyperedges of size 2; reason: the page offers both forms; the merged one has the same matrices and conductances
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), Lemma 3.4, p.10

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance
import Definitions.Def_HyperCheeger_Hypergraph_aeGraph

namespace HyperCheeger

/-- **Lemma 3.4**: if `G_H` is the AE graph of `H` and `∅ ⊊ T ⊊ V_H`, then `φ_g(T) = φ̂_h(T)`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), Lemma 3.4, p.10. -/
theorem lemma_3_4 {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) (T : Finset V)
    (hT : T.Nonempty) (hT' : T ≠ Finset.univ) :
    H.aeGraph.conductanceSet T = H.diffusionConductanceSet T := by sorry

end HyperCheeger
