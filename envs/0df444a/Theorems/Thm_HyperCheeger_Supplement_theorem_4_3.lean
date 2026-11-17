-- Prove2me | Theorems.Thm_HyperCheeger_Supplement_theorem_4_3
-- name    : HyperCheeger.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:02:07.285892+00:00
-- url     : https://prove2.me/theorems/6d6d3f4a-d2fa-4830-907f-d620456b6a84
-- title:
--   Theorem 4.3 — improved Cheeger inequality $\nu_2(H)/2\le\hat\phi_h(H)\le\sqrt{(2-\nu_2(H))\nu_2(H)}$ for non-covering hypergraphs
-- statement:
--   Let $H=(V_H,E_H,w_H)$ be a non-covering hypergraph with hyperedge weights in $[0,\infty)$ and no hyperedge of size one, let $\nu_2(H)$ be the second smallest eigenvalue of its normalized Laplacian $\mathcal L_H=D_H^{-1/2}(D_H-A_H)D_H^{-1/2}$, and let $\hat\phi_h(H)$ be its diffusion conductance. Then
--
--   $$\frac{\nu_2(H)}{2}\le\hat\phi_h(H)\le\sqrt{(2-\nu_2(H))\,\nu_2(H)}.$$
--
--   No connectivity is assumed. Since $\nu_2(H)\le 1$ for non-covering hypergraphs, the upper bound improves the bound $\sqrt{2\nu_2(H)}$ of Eq. (13), which holds for every connected hypergraph, and it extends to non-uniform hypergraphs the sharper form known for $\kappa$-uniform ones.
--
--   **Formalization Note.** $\nu_2$ and $\hat\phi_h$ are the published definitions of the mission. At a zero-degree vertex the entry of $D_H^{-1/2}$ is $0$ and the conductance of a set uses $0/0=0$.
--
--   Differences from the source:
--   - encoding: D_H^{-1/2} and the conductance of a set are undefined when a vertex or a side has degree 0 → the entry 1/√0 is 0 and the quotient 0/0 is 0; reason: w_H may vanish, so such H are in scope; a zero denominator has a zero numerator, instances with all degrees positive are unchanged
--   - encoding: a vertex set V_H of a non-covering hypergraph → a finite type V with no cardinality hypothesis; reason: non-covering supplies two distinct vertices, so 2 ≤ card V holds and ν₂ and the minimum over ∅ ⊊ S ⊊ V_H are defined
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), Theorem 4.3, eq. (14), p.11; upper bound proved in §9, pp.21–23

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Definitions.Def_HyperCheeger_Supplement_IsNonCovering

namespace HyperCheeger.Supplement

open HyperCheeger

/-- **Theorem 4.3** (Improved Cheeger's inequality for non-covering hypergraphs): if `H` is a
non-covering hypergraph, then `ν₂(H)/2 ≤ φ̂_h(H) ≤ √((2 − ν₂(H)) ν₂(H))`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), Theorem 4.3, eq. (14), p.11; upper bound proved in
§9, pp.21–23.

**Formalization Note.** `ν₂` is the published `Hypergraph.nu2` (second smallest eigenvalue of the
normalized Laplacian, with multiplicity) and `φ̂_h(H)` the published `Hypergraph.diffusionConductance`.
No connectivity is assumed, as on the page, and no positivity of weights or degrees: at a zero-degree
vertex `D^{-1/2}` has entry `0` and the conductance of a set uses `0/0 = 0`. The bound `ν₂(H) ≤ 1`
(Theorem 4.2, cited from Xu–Zhou) is used in the proof and is not a hypothesis. Non-covering already
gives `2 ≤ card V`. -/
theorem theorem_4_3 {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V)
    (hnc : IsNonCovering H) :
    H.nu2 / 2 ≤ H.diffusionConductance ∧
      H.diffusionConductance ≤ Real.sqrt ((2 - H.nu2) * H.nu2) := by sorry

end HyperCheeger.Supplement
