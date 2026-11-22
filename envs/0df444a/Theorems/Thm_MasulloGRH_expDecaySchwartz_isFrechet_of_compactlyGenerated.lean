-- Prove2me | Theorems.Thm_MasulloGRH_expDecaySchwartz_isFrechet_of_compactlyGenerated
-- name    : MasulloGRH.expDecaySchwartz_isFrechet_of_compactlyGenerated
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:44:36.552427+00:00
-- url     : https://prove2.me/theorems/94b31634-b6c1-4413-9d7f-893e4749ef34
-- title:
--   $\mathcal S_I(G)$ is Fréchet when the dual of $G^1$ is compactly generated
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, let $G^1$ be the kernel of the module, and let $I\subset\mathbb R$ be a non-empty interval. Equip $\mathcal S_I(G)$, the space of continuous $\phi$ with $|\cdot|_G^a\phi\in\mathcal S(G)$ for all $a\in I$, with its inductive topology (Definition D.3.3.3).
--
--   If the Pontryagin dual of $G^1$ is compactly generated, then $\mathcal S_I(G)$ is a Fréchet space.
--
--   This is Theorem D.3.3.7(2) (without nuclearity, which holds in general by part (1)). In this case there is a smallest relevant good subgroup: a compact $k\le G$ with $G/k$ an elementary group times $\mathbb R_{>0}$. Then $\mathcal S_I(G)=\mathcal S_I(k,G)$ is a single step, defined by countably many seminorms.
--
--   **Formalization Note.** $G^1$ is given as a subgroup of $G$ whose elements are exactly those of module $1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.3.3.3 and Theorem D.3.3.7 with its proof (pp. 805–807); cf. Theorem D.1.5.7 and F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961)

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

namespace MasulloGRH

theorem expDecaySchwartz_isFrechet_of_compactlyGenerated
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (G1 : Subgroup G) (hG1 : ∀ g : G, g ∈ G1 ↔ m g = 1)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty)
    (hcg : IsCompactlyGeneratedSubgroup (⊤ : Subgroup (PontryaginDual G1))) :
    IsFrechet (ExpDecaySchwartz G m I) := by
  sorry

end MasulloGRH
