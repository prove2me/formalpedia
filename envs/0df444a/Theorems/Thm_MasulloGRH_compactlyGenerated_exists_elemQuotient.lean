-- Prove2me | Theorems.Thm_MasulloGRH_compactlyGenerated_exists_elemQuotient
-- name    : MasulloGRH.compactlyGenerated_exists_elemQuotient
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T14:34:22.209504+00:00
-- url     : https://prove2.me/theorems/0d06e4b0-64d8-4783-9ad7-7feb79c934ff
-- title:
--   Compactly generated LCA groups have small subgroups with elementary quotient
-- statement:
--   Let $H$ be a second countable Hausdorff locally compact abelian group which is compactly generated, i.e. generated as a group by a compact subset. Then $H$ has arbitrarily small compact subgroups with elementary quotient: for every neighbourhood $U$ of the identity there is a compact subgroup $K\subseteq U$ such that $H/K$ is isomorphic, as a topological group, to an elementary group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ with $F=\prod_{i}\mathbb Z/d_i\mathbb Z$ a finite abelian group ($d_i\ne0$).
--
--   Equivalently, there is a continuous, open, surjective homomorphism $\pi\colon H\to\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ whose kernel is exactly $K$.
-- source:
--   Hewitt–Ross, Abstract Harmonic Analysis I, Theorems 9.8 and 24.x (structure of compactly generated LCA groups; Pontryagin duality); used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.4–D.1.5

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem compactlyGenerated_exists_elemQuotient
    (H : Type*) [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    (hcg : ∃ C : Set H, IsCompact C ∧ Subgroup.closure C = ⊤)
    (U : Set H) (hU : U ∈ nhds (1 : H)) :
    ∃ K : Subgroup H, IsCompact (K : Set H) ∧ (K : Set H) ⊆ U ∧
      ∃ (m n r s : ℕ) (d : Fin s → ℕ) (π : H →* Multiplicative (ElemGroup m n r s d)),
        (∀ i, d i ≠ 0) ∧ Continuous π ∧ IsOpenMap π ∧ Function.Surjective π ∧
          ∀ x, π x = 1 ↔ x ∈ K := by
  sorry

end MasulloGRH
