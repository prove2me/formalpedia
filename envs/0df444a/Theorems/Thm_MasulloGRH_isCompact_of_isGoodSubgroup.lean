-- Prove2me | Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
-- name    : MasulloGRH.isCompact_of_isGoodSubgroup
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T14:38:21.559232+00:00
-- url     : https://prove2.me/theorems/b40ac3c5-1d13-4924-8ad3-5e6204b7ea8b
-- title:
--   Good subgroups are compact
-- statement:
--   Let $G$ be a Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$, and let $k\subseteq G$ be a **good** subgroup. That is, $k$ is closed in $G$, and its annihilator
--
--   $$
--   k^\perp=\{\chi\in\widehat G:\ \chi(y)=1\ \text{for all } y\in k\}
--   $$
--
--   is an open and compactly generated subgroup of $\widehat G$. Then $k$ is compact.
--
--   This is the implication "$k^\perp$ open $\Rightarrow$ $k$ compact" recorded in Definition D.1.5.1(1), where openness of $k^\perp$ is noted to be equivalent to compactness of $k$. It is what allows integration against the normalized Haar measure of $k$, for instance in the averaging operators $A_{\Gamma,k}$ attached to structural pairs.
--
--   **Formalization Note** $\widehat G$ is Mathlib's `PontryaginDual G` with the compact-open topology. Only the openness part of goodness is needed mathematically. The compact-generation clause is part of the hypothesis `IsGoodSubgroup k` as defined on the platform.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.1.5.1(1) (p. 760) and Lemma D.1.4.6(1),(4) (p. 758)

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem isCompact_of_isGoodSubgroup
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsCompact (k : Set G) := by
  sorry

end MasulloGRH
