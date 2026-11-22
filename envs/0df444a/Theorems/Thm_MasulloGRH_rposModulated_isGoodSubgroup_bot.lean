-- Prove2me | Theorems.Thm_MasulloGRH_rposModulated_isGoodSubgroup_bot
-- name    : MasulloGRH.rposModulated_isGoodSubgroup_bot
-- status  : Proved
-- author  : @kirisame
-- created : 2026-11-21T18:58:03.887557+00:00
-- url     : https://prove2.me/theorems/cccc0fa5-fb3a-49cb-8e04-de16692a8164
-- title:
--   If $\widehat{G^1}$ is compactly generated, the trivial subgroup of an $\mathbb R_{>0}$-modulated group is good
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, and let $G^1$ be the kernel of the module. Suppose that the Pontryagin dual $\widehat{G^1}$ is compactly generated. Then the trivial subgroup of $G$ is good: its annihilator, which is all of $\widehat G$, is open and compactly generated.
--
--   Equivalently, $G$ itself is an elementary abelian Lie group. The dual of the compact group $G^1$ is discrete, so it is finitely generated, and finitely many characters of $G^1$ detect every small compact subgroup of $G$. This is the step of the proof of Theorem D.3.3.7(2) that allows the choice $k=0$, so that $\mathcal S_I(G)=\mathcal S_I(0,G)$ is a single stage.
--
--   **Formalization Note** $G^1$ is given as a subgroup of $G$ whose elements are exactly those of module $1$. Compact generation of $\widehat{G^1}$ is expressed for its top subgroup, in the sense of Definition D.1.4.1.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3, proof of Theorem D.3.3.7(2), p. 810 (“In this case $G=\mathbb R_{>0}\times G^1$ is an elementary abelian Lie group, so we can take $k=0$”)

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

namespace MasulloGRH

theorem rposModulated_isGoodSubgroup_bot
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (G1 : Subgroup G) (hG1 : ∀ g : G, g ∈ G1 ↔ m g = 1)
    (hcg : IsCompactlyGeneratedSubgroup (⊤ : Subgroup (PontryaginDual G1))) :
    IsGoodSubgroup (⊥ : Subgroup G) := by
  sorry

end MasulloGRH
