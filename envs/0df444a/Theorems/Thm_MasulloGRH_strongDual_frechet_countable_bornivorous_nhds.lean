-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_frechet_countable_bornivorous_nhds
-- name    : MasulloGRH.strongDual_frechet_countable_bornivorous_nhds
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:27:13.048538+00:00
-- url     : https://prove2.me/theorems/0cbcbb7e-829c-45ae-a07a-a7cb4639985e
-- title:
--   Countable bornivorous intersections of neighbourhoods in the strong dual of a Fréchet space
-- statement:
--   Let $E$ be a Fréchet space over $\mathbb C$ and $E'_\beta$ its strong dual. Let $(U_n)_{n\in\mathbb N}$ be closed, balanced, convex $0$-neighbourhoods in $E'_\beta$ such that $V = \bigcap_n U_n$ absorbs every bounded subset of $E'_\beta$. Then
--
--   $$V = \bigcap_{n} U_n \text{ is a } 0\text{-neighbourhood in } E'_\beta.$$
--
--   This is the second half of the $(DF)$ property of the strong dual of a metrizable locally convex space (Grothendieck; Schaefer IV.8.1).
-- source:
--   H. H. Schaefer, Topological Vector Spaces, IV.8.1 and its proof (the strong dual of a metrizable locally convex space is a (DF)-space); A. Grothendieck, Sur les espaces (F) et (DF), Summa Brasil. Math. 3 (1954); used in A. M. Masullo, The Music of the Primes (draft), Appendix C, Lemma C.2.4.11

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_frechet_countable_bornivorous_nhds (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (U : ℕ → Set (StrongDual ℂ E))
    (hU : ∀ n, U n ∈ nhds (0 : StrongDual ℂ E) ∧ IsClosed (U n) ∧
      Balanced ℂ (U n) ∧ Convex ℝ (U n))
    (hbor : ∀ S : Set (StrongDual ℂ E), Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) :
    (⋂ n, U n) ∈ nhds (0 : StrongDual ℂ E) := by sorry

end MasulloGRH
