-- Prove2me | Theorems.Thm_MasulloGRH_expDecaySchwartz_exists_good_invariant
-- name    : MasulloGRH.expDecaySchwartz_exists_good_invariant
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T18:21:50.479175+00:00
-- url     : https://prove2.me/theorems/314343fe-50cf-4e4b-858d-710c630592bd
-- title:
--   Every element of $\mathcal S_I(G)$ is invariant under a good subgroup
-- statement:
--   Let $(G,|\cdot|_G)$ be a second countable Hausdorff locally compact abelian group with a surjective module $|\cdot|_G\colon G\to\mathbb R_{>0}$, and let $I\subset\mathbb R$ be a non-empty interval. Write $\mathcal S_I(k,G)$ for the stage of $k$-invariant elements of $\mathcal S_I(G)$, with the projective topology of the maps $T_a\phi=|\cdot|_G^a\phi\in\mathcal S(G/k)$, $a\in I$ (Definition D.3.3.3).
--
--   Every $\phi\in\mathcal S_I(G)$ is $k$-invariant for some good subgroup $k$. Indeed, $|\cdot|_G^a\phi\in\mathcal S(G)$ for some $a\in I$ is invariant under some good subgroup, and so is $|\cdot|_G$, being trivial on compact subgroups (Definition D.3.3.3).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.3: Definition D.3.3.3, Example D.3.3.5, Remark D.3.3.8 (pp. 804–807)

import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem expDecaySchwartz_exists_good_invariant
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (ϕ : ExpDecaySchwartz G m I) :
    ∃ k : Subgroup G, IsGoodSubgroup k ∧ ϕ ∈ expDecayInvSubmodule G m I k := by
  sorry

end MasulloGRH
