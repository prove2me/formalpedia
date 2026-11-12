-- Prove2me | Theorems.Thm_HyperCheeger_theorem_4_1
-- name    : HyperCheeger.theorem_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:03:27.959124+00:00
-- url     : https://prove2.me/theorems/d1f83f3a-16a8-467f-bd3d-280466ce05b7
-- title:
--   Theorem 4.1 — Cheeger's inequality for hypergraphs: $\nu_2(H)/\Upsilon_H\le\phi_h(H)\le\sqrt{2\nu_2(H)}$
-- statement:
--   Let $H$ be a connected hypergraph, with weights in $[0,\infty)$ and hyperedges of any size other than one, on at least two vertices. Let $\nu_2(H)$ be the second smallest eigenvalue of its normalized Laplacian $\mathcal L_H$, and let $\Upsilon_H$ be its rank. Then
--
--   $$\frac{\nu_2(H)}{\Upsilon_H}\le\phi_h(H)\le\sqrt{2\nu_2(H)}.$$
--
--   This relates the conductance of a hypergraph to a single eigenvalue of a fixed symmetric matrix. The upper bound does not depend on the rank.
--
--   **Formalization Note.** There is no positivity of weights or degrees and no uniformity assumption. When $H$ has a zero-degree vertex or is disconnected in weight, $\nu_2(H)=0=\phi_h(H)$.
--
--   Differences from the source:
--   - encoding: D_H^{-1/2} and the conductance of a set are undefined when a vertex or a side has degree 0 → the entry 1/√0 is 0 and the quotient 0/0 is 0; reason: w_H may vanish, so such H are in scope; a zero denominator has a zero numerator, instances with all degrees positive are unchanged, and for connected H both sides of the inequalities are 0 on the new instances
--   - encoding: a set of n vertices, with ν₂ and a proper nonempty subset implicitly available → a finite type V with 2 ≤ card V; reason: ν₂ needs two eigenvalues and the minimum over ∅ ⊊ S ⊊ V needs a set S; connectedness already excludes card V = 1
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), Theorem 4.1, eq. (11), p.10

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_conductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2

namespace HyperCheeger

/-- **Theorem 4.1** (Cheeger's inequality for hypergraphs): if `H` is a connected hypergraph, `ν₂(H)` is
the second smallest eigenvalue of its normalized Laplacian `𝓛_H` and `Υ_H` is its rank, then
`ν₂(H)/Υ_H ≤ φ_h(H) ≤ √(2ν₂(H))`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), Theorem 4.1, eq. (11), p.10.

**Formalization Note.** Weights lie in `[0, ∞)`, with no positivity of weights or degrees and hyperedges of
any size other than one. At a zero-degree vertex `D^{-1/2}` has entry `0` and the conductance of a set uses
`0/0 = 0`, where the paper is undefined; both sides are then `0`. `2 ≤ card V` is what `ν₂` and `φ_h(H)` need:
connectedness already excludes `card V = 1`. -/
theorem theorem_4_1 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (H : Hypergraph V) (hconn : H.IsConnected) :
    H.nu2 / (H.rank : ℝ) ≤ H.conductance ∧ H.conductance ≤ Real.sqrt (2 * H.nu2) := by sorry

end HyperCheeger
