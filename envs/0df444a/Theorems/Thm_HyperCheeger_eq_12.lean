-- Prove2me | Theorems.Thm_HyperCheeger_eq_12
-- name    : HyperCheeger.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:59.335008+00:00
-- url     : https://prove2.me/theorems/734b7ef2-38aa-428a-962c-99f949cde5a1
-- title:
--   Eq. (12) — Cheeger's inequality for the AE graph
-- statement:
--   Let $H$ be a connected hypergraph on at least two vertices, and let $G_H$ be its AE graph. Then
--
--   $$\frac{\nu_2(H)}{2}\le\phi_g(G_H)\le\sqrt{2\nu_2(H)}.$$
--
--   Note the eigenvalue is that of $H$ and the conductance is that of $G_H$. This is the first step of the proof of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: D_H^{-1/2} and the conductance of a set are undefined when a vertex or a side has degree 0 → the entry 1/√0 is 0 and the quotient 0/0 is 0; reason: w_H may vanish, so such H are in scope; a zero denominator has a zero numerator, instances with all degrees positive are unchanged, and for connected H both sides of the inequalities are 0 on the new instances
--   - encoding: a set of n vertices, with ν₂ and a proper nonempty subset implicitly available → a finite type V with 2 ≤ card V; reason: ν₂ needs two eigenvalues and the minimum over ∅ ⊊ S ⊊ V needs a set S; connectedness already excludes card V = 1
--   - encoding: the AE graph has parallel edges, or equivalently one edge with the added weight → the merged form, aeGraph, a hypergraph with all hyperedges of size 2; reason: the page offers both forms; the merged one has the same matrices and conductances
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), proof of Theorem 4.1, eq. (12), p.11

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_conductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Definitions.Def_HyperCheeger_Hypergraph_aeGraph

namespace HyperCheeger

/-- **Eq. (12)**: `ν₂(H)/2 ≤ φ_g(G_H) ≤ √(2ν₂(H))` for a connected hypergraph `H` with AE graph `G_H`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), proof of Theorem 4.1, eq. (12), p.11. -/
theorem eq_12 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (H : Hypergraph V) (hconn : H.IsConnected) :
    H.nu2 / 2 ≤ H.aeGraph.conductance ∧ H.aeGraph.conductance ≤ Real.sqrt (2 * H.nu2) := by sorry

end HyperCheeger
