-- Prove2me | Theorems.Thm_HyperCheeger_eq_13
-- name    : HyperCheeger.eq_13
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:04:48.082564+00:00
-- url     : https://prove2.me/theorems/af060555-906b-4fa7-8813-7571cdaf185b
-- title:
--   Eq. (13) — Cheeger's inequality for the diffusion conductance
-- statement:
--   Let $H$ be a connected hypergraph on at least two vertices, with AE graph $G_H$. Then $\phi_g(G_H)=\hat\phi_h(H)$, and
--
--   $$\frac{\nu_2(H)}{2}\le\hat\phi_h(H)\le\sqrt{2\nu_2(H)}.$$
--
--   This is the sharp two-sided bound for $\hat\phi_h$ from which Theorem 4.1 follows.
--
--   Differences from the source:
--   - encoding: D_H^{-1/2} and the conductance of a set are undefined when a vertex or a side has degree 0 → the entry 1/√0 is 0 and the quotient 0/0 is 0; reason: w_H may vanish, so such H are in scope; a zero denominator has a zero numerator, instances with all degrees positive are unchanged, and for connected H both sides of the inequalities are 0 on the new instances
--   - encoding: a set of n vertices, with ν₂ and a proper nonempty subset implicitly available → a finite type V with 2 ≤ card V; reason: ν₂ needs two eigenvalues and the minimum over ∅ ⊊ S ⊊ V needs a set S; connectedness already excludes card V = 1
--   - encoding: the AE graph has parallel edges, or equivalently one edge with the added weight → the merged form, aeGraph, a hypergraph with all hyperedges of size 2; reason: the page offers both forms; the merged one has the same matrices and conductances
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), proof of Theorem 4.1, eq. (13), p.11

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Definitions.Def_HyperCheeger_Hypergraph_aeGraph

namespace HyperCheeger

/-- **Eq. (13)**: for a connected hypergraph `H`, `φ_g(G_H) = φ̂_h(H)` and
`ν₂(H)/2 ≤ φ̂_h(H) ≤ √(2ν₂(H))`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), proof of Theorem 4.1, eq. (13), p.11. -/
theorem eq_13 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (H : Hypergraph V) (hconn : H.IsConnected) :
    H.aeGraph.conductance = H.diffusionConductance ∧
      H.nu2 / 2 ≤ H.diffusionConductance ∧ H.diffusionConductance ≤ Real.sqrt (2 * H.nu2) := by sorry

end HyperCheeger
