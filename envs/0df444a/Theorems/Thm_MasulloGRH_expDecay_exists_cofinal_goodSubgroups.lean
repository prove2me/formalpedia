-- Prove2me | Theorems.Thm_MasulloGRH_expDecay_exists_cofinal_goodSubgroups
-- name    : MasulloGRH.expDecay_exists_cofinal_goodSubgroups
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:21:43.595332+00:00
-- url     : https://prove2.me/theorems/6b7e82de-64bd-422a-a702-fbaf32cf7da8
-- title:
--   A cofinal decreasing sequence of good subgroups of a modulated group
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module. Then there is a decreasing sequence $k_0\supseteq k_1\supseteq\cdots$ of good subgroups of $G$ (closed, with open compactly generated orthogonal) such that every good subgroup $k$ contains some $k_N$.
--
--   This is Remark D.3.3.8. Since $G\simeq\mathbb R_{>0}	imes G^1$ is compactly generated, it follows from the cofinal structural pairs of $G$ (cf. `exists_cofinal_structuralPairs`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3: Definition D.3.3.3, Example D.3.3.5, Remark D.3.3.8 (pp. 804–807)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecay_exists_cofinal_goodSubgroups
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
:
    ∃ k : ℕ → Subgroup G, (∀ N, IsGoodSubgroup (k N)) ∧ Antitone k ∧
      ∀ k' : Subgroup G, IsGoodSubgroup k' → ∃ N, k N ≤ k' := by
  sorry

end MasulloGRH
