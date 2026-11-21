-- Prove2me | Theorems.Thm_MasulloGRH_expDecaySchwartz_structure
-- name    : MasulloGRH.expDecaySchwartz_structure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T03:34:30.566003+00:00
-- url     : https://prove2.me/theorems/9b8d72ae-c1dc-4fed-8aae-ce6cecc0b12e
-- title:
--   Theorem D.3.3.7 (2)–(3) — $\mathcal S_I(G)$ is a complete, nuclear, Montel strict LF-space
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, let $G^1$ be the kernel of the module, and let $I\subset\mathbb R$ be a non-empty interval. Let $\mathcal S_I(G)$ be the space of continuous functions $\phi$ on $G$ with $|\cdot|_G^a\phi\in\mathcal S(G)$ for all $a\in I$, with its inductive topology.
--
--   1. $\mathcal S_I(G)$ is a Hausdorff locally convex space that is complete, nuclear and Montel, and a strict LF-space. In particular it is barrelled and bornological.
--   2. If the dual group of $G^1$ is compactly generated, then $\mathcal S_I(G)$ is a nuclear Fréchet space.
--   3. The strong dual $\mathcal S_I(G)'_\beta$ is complete, nuclear and Montel.
--
--   The theorem applies to $G=C_F$ and $G=J_{F,S}$ with the idelic norms, and gives the topological properties of the spaces that contain the $\theta$-functions.
--
--   **Formalization Note** $G^1$ is given as a subgroup of $G$ whose elements are exactly those of module $1$. The hypothesis of item 2 is that the Pontryagin dual of $G^1$ is compactly generated; nuclearity in that case is contained in item 1.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3, Theorem D.3.3.7 (Structure of S_I(G) for R_{>0}-modulated groups), parts (2) and (3), pp. 806–807

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

namespace MasulloGRH

theorem expDecaySchwartz_structure
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (G1 : Subgroup G) (hG1 : ∀ g : G, g ∈ G1 ↔ m g = 1)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) :
    (IsHLCS (ExpDecaySchwartz G m I) ∧ IsCompleteTVS (ExpDecaySchwartz G m I) ∧
      IsNuclear (ExpDecaySchwartz G m I) ∧ IsMontel (ExpDecaySchwartz G m I) ∧
      IsStrictLF (ExpDecaySchwartz G m I) ∧ BarrelledSpace ℂ (ExpDecaySchwartz G m I) ∧
      IsBornological (ExpDecaySchwartz G m I)) ∧
    (IsCompactlyGeneratedSubgroup (⊤ : Subgroup (PontryaginDual G1)) →
      IsFrechet (ExpDecaySchwartz G m I)) ∧
    (IsCompleteTVS (StrongDual ℂ (ExpDecaySchwartz G m I)) ∧
      IsNuclear (StrongDual ℂ (ExpDecaySchwartz G m I)) ∧
      IsMontel (StrongDual ℂ (ExpDecaySchwartz G m I))) := by sorry

end MasulloGRH
