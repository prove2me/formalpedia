-- Prove2me | Theorems.Thm_HyperCheeger_eq_2
-- name    : HyperCheeger.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:52.214655+00:00
-- url     : https://prove2.me/theorems/1523bb72-ad03-4ace-b994-2cfb30516688
-- title:
--   Eq. (2) — $\phi_h(H)\le\hat\phi_h(H)\le(\Upsilon_H/2)\phi_h(H)$
-- statement:
--   Let $H$ be a hypergraph of rank $\Upsilon_H$ on at least two vertices. Then
--
--   $$\phi_h(H)\le\hat\phi_h(H)\le\frac{\Upsilon_H}{2}\,\phi_h(H).$$
--
--   This is what turns the lower bound on $\hat\phi_h(H)$ into the lower bound of Theorem 4.1, at the cost of the rank.
--
--   Differences from the source:
--   - encoding: the conductance of a set is undefined when a side has volume 0 → the quotient 0/0 is 0; reason: w_H may vanish; a zero denominator has a zero numerator, and sets with both volumes positive are unchanged
--   - encoding: a set of n vertices, with a proper nonempty subset implicitly available → a finite type V with 2 ≤ card V; reason: the minimum over ∅ ⊊ S ⊊ V is over an empty range otherwise
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), eq. (2), p.7

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance

namespace HyperCheeger

/-- **Eq. (2)**: `φ_h(H) ≤ φ̂_h(H) ≤ (Υ_H/2) φ_h(H)`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), eq. (2), p.7. -/
theorem eq_2 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) (H : Hypergraph V) :
    H.conductance ≤ H.diffusionConductance ∧
      H.diffusionConductance ≤ (H.rank : ℝ) / 2 * H.conductance := by sorry

end HyperCheeger
