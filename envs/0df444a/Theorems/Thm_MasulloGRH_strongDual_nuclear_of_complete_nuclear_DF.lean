-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_nuclear_of_complete_nuclear_DF
-- name    : MasulloGRH.strongDual_nuclear_of_complete_nuclear_DF
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:19:10.933795+00:00
-- url     : https://prove2.me/theorems/d3acdbe0-33b4-48d8-9b45-b842962ebe72
-- title:
--   The strong dual of a complete nuclear (DF)-space is nuclear
-- statement:
--   Let $G$ be a complete nuclear locally convex space over $\mathbb C$ which is a $(DF)$-space, i.e.
--
--   1. $G$ has a fundamental sequence of bounded sets $B_0, B_1, \dots$ (every bounded set lies in some $B_n$), and
--   2. every countable intersection $\bigcap_n U_n$ of closed, balanced, convex $0$-neighbourhoods which absorbs all bounded sets is itself a $0$-neighbourhood.
--
--   Then the strong dual $G'_\beta$ is nuclear (indeed a nuclear Fréchet space). This is Schaefer, *Topological Vector Spaces*, IV.9.6.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, Lemma C.2.4.11; H. H. Schaefer, Topological Vector Spaces, IV.6.1 (strong dual of bornological space complete), IV.8.1 (strong dual of metrizable LCS is (DF)), IV.9.6 (strong dual of complete nuclear (DF)-space is nuclear)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_nuclear_of_complete_nuclear_DF (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G)) :
    IsNuclear (StrongDual ℂ G) := by sorry

end MasulloGRH
