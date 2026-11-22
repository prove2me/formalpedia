-- Prove2me | Theorems.Thm_MasulloGRH_isStructuralPair_comap_quotient
-- name    : MasulloGRH.isStructuralPair_comap_quotient
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T19:23:24.137178+00:00
-- url     : https://prove2.me/theorems/5ef4ae39-d1f0-4d85-93c7-c1062e35dca4
-- title:
--   Structural pairs pull back along G/k′ → G/k
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group, let $k'\subseteq k$ be good subgroups, and let $p\colon G/k'\to G/k$ be the projection. If $(\Gamma,k_1)$ is a structural pair in $G/k$, then
--   $$(p^{-1}\Gamma,\ p^{-1}k_1)\ \text{is a structural pair in } G/k'.$$
--   Structural pairs thus pull back along quotient maps with compact kernel. This is used to pull back Schwartz–Bruhat functions along $p$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.1.5.1 and §D.1.5

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem isStructuralPair_comap_quotient
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') (hle : k' ≤ k)
    (Γ k₁ : Subgroup (G ⧸ k)) (hs : IsStructuralPair Γ k₁) :
    IsStructuralPair (Γ.comap (QuotientGroup.map k' k (MonoidHom.id G) hle))
      (k₁.comap (QuotientGroup.map k' k (MonoidHom.id G) hle)) := by
  sorry

end MasulloGRH
