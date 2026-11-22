-- Prove2me | Theorems.Thm_MasulloGRH_annihilator_isCompactlyGenerated
-- name    : MasulloGRH.annihilator_isCompactlyGenerated
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T14:34:21.425813+00:00
-- url     : https://prove2.me/theorems/f2ef5e18-993d-4c16-af4b-8ade0787ab8e
-- title:
--   Annihilator of a compact subgroup with elementary quotient is compactly generated
-- statement:
--   Let $G$ be a second countable Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$ (continuous characters $G\to\mathbb T$ with the compact-open topology). Let $k\subseteq G$ be a compact subgroup and $\Gamma\supseteq k$ an open subgroup of $G$ such that $\Gamma/k$ is an elementary group: there is a continuous, open, surjective homomorphism $\pi\colon\Gamma\to\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite) with kernel $k$.
--
--   Then the annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is a compactly generated subgroup of $\widehat G$: there is a compact set $C\subseteq k^\perp$ generating $k^\perp$ which is a neighbourhood of the identity in $k^\perp$ (i.e. $V\cap k^\perp\subseteq C$ for some identity neighbourhood $V$ of $\widehat G$).
-- source:
--   Hewitt–Ross, Abstract Harmonic Analysis I, Theorems 9.8 and 24.x (structure of compactly generated LCA groups; Pontryagin duality); used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.4–D.1.5

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem annihilator_isCompactlyGenerated
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (k Γ : Subgroup G) (hk : IsCompact (k : Set G)) (hΓ : IsOpen (Γ : Set G)) (hkΓ : k ≤ Γ)
    {m n r s : ℕ} {d : Fin s → ℕ} (π : ↥Γ →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation Γ k π) :
    ∃ A : Subgroup (PontryaginDual G), (A : Set (PontryaginDual G)) = annihilator k ∧
      IsCompactlyGeneratedSubgroup A := by
  sorry

end MasulloGRH
