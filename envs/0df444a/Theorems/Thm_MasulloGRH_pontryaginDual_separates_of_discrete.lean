-- Prove2me | Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_discrete
-- name    : MasulloGRH.pontryaginDual_separates_of_discrete
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T15:07:49.548781+00:00
-- url     : https://prove2.me/theorems/9a9a2532-0f04-42ad-8ef2-803dba7789dc
-- title:
--   Characters of a discrete abelian group separate points from subgroups
-- statement:
--   Let $G$ be an abelian group equipped with the discrete topology, and write $\widehat G=\operatorname{Hom}_{\mathrm{cont}}(G,\mathbb T)$ for its Pontryagin dual, where $\mathbb T=\{z\in\mathbb C:|z|=1\}$. Let $H\subseteq G$ be any subgroup and let $g\in G\setminus H$. Then there is a character $\chi\in\widehat G$ with
--
--   $$
--   \chi(h)=1\ \text{ for all } h\in H\qquad\text{and}\qquad \chi(g)\neq 1 .
--   $$
--
--   Equivalently, $H^{\perp\perp}=H$ for every subgroup $H$ of a discrete abelian group, where $H^\perp=\{\chi\in\widehat G:\chi(H)=1\}$ and $\Gamma^\perp=\{x\in G:\chi(x)=1 \text{ for all }\chi\in\Gamma\}$. This is the discrete case of Lemma D.1.4.6(1) in Masullo's Appendix D (annihilator duality for Hausdorff locally compact abelian groups), and in particular characters of a discrete abelian group separate points. It is a building block toward the compactness of good subgroups (`MasulloGRH.isCompact_of_isGoodSubgroup`).
--
--   **Formalization Note** The dual is Mathlib's `PontryaginDual G`, the group of continuous monoid homomorphisms $G\to$ `Circle`; for the discrete topology every homomorphism is continuous.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.4.6(1) (p. 758): the inclusion $H^{\perp\perp}\subseteq H$ in the special case of a discrete group; cf. A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis (2nd ed., Springer 2014), Prop. 3.6.1

import Mathlib.Topology.Algebra.PontryaginDual

set_option autoImplicit false

namespace MasulloGRH

theorem pontryaginDual_separates_of_discrete
    (G : Type*) [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (H : Subgroup G) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 := by
  sorry

end MasulloGRH
