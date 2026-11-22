-- Prove2me | Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_compact
-- name    : MasulloGRH.pontryaginDual_separates_of_compact
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T15:07:49.064736+00:00
-- url     : https://prove2.me/theorems/8eddb08d-0597-4011-9a05-79dd8417e29d
-- title:
--   Characters of a compact abelian group separate points from closed subgroups
-- statement:
--   Let $G$ be a compact Hausdorff abelian topological group, and write $\widehat G$ for its Pontryagin dual, the group of continuous homomorphisms $G\to\mathbb T=\{z\in\mathbb C:|z|=1\}$. Let $H\subseteq G$ be a closed subgroup and let $g\in G\setminus H$. Then there is a continuous character $\chi\in\widehat G$ with
--
--   $$
--   \chi(h)=1\ \text{ for all } h\in H\qquad\text{and}\qquad \chi(g)\neq 1 .
--   $$
--
--   Equivalently, $H^{\perp\perp}=H$ for every closed subgroup $H$ of a compact Hausdorff abelian group (with $H^\perp$ and $\Gamma^\perp$ the annihilators as in Masullo's (D.1.4.6)–(D.1.4.7)). Taking $H=\{1\}$, the continuous characters of a compact Hausdorff abelian group separate points. This is the compact case of Lemma D.1.4.6(1) in Masullo's Appendix D and is a building block toward the compactness of good subgroups (`MasulloGRH.isCompact_of_isGoodSubgroup`).
--
--   **Formalization Note** The dual is Mathlib's `PontryaginDual G`, the group of continuous monoid homomorphisms $G\to$ `Circle`. No second-countability or metrizability hypothesis is imposed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.4.6(1) (p. 758): the inclusion $H^{\perp\perp}\subseteq H$ in the special case of a compact group; cf. A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis (2nd ed., Springer 2014), Prop. 3.6.1, and the Peter–Weyl theorem

import Mathlib.Topology.Algebra.PontryaginDual

set_option autoImplicit false

namespace MasulloGRH

theorem pontryaginDual_separates_of_compact
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 := by
  sorry

end MasulloGRH
