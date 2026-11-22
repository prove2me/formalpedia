-- Prove2me | Theorems.Thm_MasulloGRH_quotient_goodSubgroup_dual_compactlyGenerated
-- name    : MasulloGRH.quotient_goodSubgroup_dual_compactlyGenerated
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T19:02:23.39763+00:00
-- url     : https://prove2.me/theorems/6e35abed-5ea5-4f93-a003-7454ac447d92
-- title:
--   The dual of G/k is compactly generated for a good subgroup k
-- statement:
--   Let $G$ be a second-countable, locally compact, Hausdorff abelian group and $k$ a good subgroup: $k$ is closed and its annihilator $k^\perp\subseteq\widehat G$ is open and compactly generated. Then the Pontryagin dual of $G/k$ is compactly generated:
--   $$\widehat{G/k}\ \text{is compactly generated}.$$
--   This is because $\widehat{G/k}\cong k^\perp$ as topological groups (Pontryagin duality for closed subgroups). It is the duality input that makes the trivial subgroup of $G/k$ good.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.4–D.1.5 (Definitions D.1.4.5, D.1.5.1)

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem quotient_goodSubgroup_dual_compactlyGenerated
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsCompactlyGeneratedSubgroup (⊤ : Subgroup (PontryaginDual (G ⧸ k))) := by
  sorry

end MasulloGRH
