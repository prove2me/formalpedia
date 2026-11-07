-- Prove2me | Theorems.Thm_HyperCheeger_theorem_3_1
-- name    : HyperCheeger.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:47.040973+00:00
-- url     : https://prove2.me/theorems/b6f9414f-46cd-4c6f-961e-fb891b8139f9
-- title:
--   Theorem 3.1 — Cheeger's inequality for 2-graphs
-- statement:
--   Let $G$ be a connected 2-graph with weights in $[0,\infty)$, on at least two vertices, and let $\nu_2(G)$ be the second smallest eigenvalue of its normalized Laplacian $\mathcal L_G$. Then
--
--   $$\frac{\nu_2(G)}{2}\le\phi_g(G)\le\sqrt{2\nu_2(G)}.$$
--
--   This is the classical inequality of Alon–Milman and Alon, cited by the paper and transferred to hypergraphs in its Section 4.
--
--   **Formalization Note.** Connectedness ignores weights, so $G$ may have zero-degree vertices or be disconnected in weight; then both sides vanish. The Proved platform theorem `MarkovMixing.cheeger_inequality` covers the mathematics for irreducible reversible chains and is a reference item of the mission; it is not assumed here.
--
--   Differences from the source:
--   - encoding: D_H^{-1/2} and the conductance of a set are undefined when a vertex or a side has degree 0 → the entry 1/√0 is 0 and the quotient 0/0 is 0; reason: w_H may vanish, so such H are in scope; a zero denominator has a zero numerator, instances with all degrees positive are unchanged, and for connected H both sides of the inequalities are 0 on the new instances
--   - encoding: a set of n vertices, with ν₂ and a proper nonempty subset implicitly available → a finite type V with 2 ≤ card V; reason: ν₂ needs two eigenvalues and the minimum over ∅ ⊊ S ⊊ V needs a set S; connectedness already excludes card V = 1
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), Theorem 3.1, eq. (8), p.9

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_conductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2

namespace HyperCheeger

/-- **Theorem 3.1** (Cheeger's inequality for 2-graphs): if `G` is a connected 2-graph and `ν₂(G)` is
the second smallest eigenvalue of its normalized Laplacian, then
`ν₂(G)/2 ≤ φ_g(G) ≤ √(2ν₂(G))`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), Theorem 3.1, eq. (8), p.9
(the paper cites Alon–Milman 1985 and Alon 1986).

**Formalization Note.** `φ_g` is `conductance` on a hypergraph with `IsTwoGraph`. Weights may vanish, so
`G` may have zero-degree vertices or be disconnected in weight; then both sides are `0`. -/
theorem theorem_3_1 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (G : Hypergraph V) (hG : G.IsTwoGraph) (hconn : G.IsConnected) :
    G.nu2 / 2 ≤ G.conductance ∧ G.conductance ≤ Real.sqrt (2 * G.nu2) := by sorry

end HyperCheeger
