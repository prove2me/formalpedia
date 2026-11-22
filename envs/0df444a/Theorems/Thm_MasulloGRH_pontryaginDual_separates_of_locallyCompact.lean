-- Prove2me | Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_locallyCompact
-- name    : MasulloGRH.pontryaginDual_separates_of_locallyCompact
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T15:32:19.60623+00:00
-- url     : https://prove2.me/theorems/dee6d4bc-87e5-4503-b220-e154a0089e17
-- title:
--   Gelfand–Raikov: characters of a locally compact abelian group separate points from closed subgroups
-- statement:
--   Let $G$ be a Hausdorff locally compact abelian group, and write $\widehat G$ for its Pontryagin dual, the group of continuous homomorphisms $G\to\mathbb T=\{z\in\mathbb C:|z|=1\}$. Let $H\subseteq G$ be a closed subgroup and let $g\in G\setminus H$. Then there is a continuous character $\chi\in\widehat G$ with
--
--   $$
--   \chi(h)=1\ \text{ for all } h\in H\qquad\text{and}\qquad \chi(g)\neq 1 .
--   $$
--
--   Equivalently, $H^{\perp\perp}=H$ for every closed subgroup $H$ of $G$, where $H^\perp=\{\chi\in\widehat G:\chi(H)=1\}$ and $\Gamma^\perp=\{x\in G:\chi(x)=1\ \text{for all}\ \chi\in\Gamma\}$ as in Masullo's (D.1.4.6)–(D.1.4.7). Taking $H=\{1\}$ gives the Gelfand–Raikov theorem: the continuous characters of a Hausdorff locally compact abelian group separate points. This is Lemma D.1.4.6(1) of Masullo's Appendix D, and it is a basic input for the compactness of good subgroups (`MasulloGRH.isCompact_of_isGoodSubgroup`).
--
--   **Formalization Note** The dual is Mathlib's `PontryaginDual G`, the group of continuous monoid homomorphisms $G\to$ `Circle` with the compact-open topology. No second-countability or metrizability hypothesis is imposed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.4.6(1) (p. 758): the inclusion $H^{\perp\perp}\subseteq H$; cf. A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis (2nd ed., Springer 2014), Prop. 3.6.1, and the Gelfand–Raikov theorem (Hewitt–Ross, Abstract Harmonic Analysis I, Thm. 22.17)

import Mathlib.Topology.Algebra.PontryaginDual

set_option autoImplicit false

namespace MasulloGRH

theorem pontryaginDual_separates_of_locallyCompact
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 := by
  sorry

end MasulloGRH
