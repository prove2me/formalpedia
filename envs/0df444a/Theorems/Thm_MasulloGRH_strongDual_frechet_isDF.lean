-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_frechet_isDF
-- name    : MasulloGRH.strongDual_frechet_isDF
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:19:09.685323+00:00
-- url     : https://prove2.me/theorems/cbda3fef-a330-447c-84ba-e34f4e5f16a7
-- title:
--   The strong dual of a Fréchet space is a (DF)-space
-- statement:
--   Let $E$ be a Fréchet space over $\mathbb C$ and $E'_\beta$ its strong dual. Then $E'_\beta$ is a $(DF)$-space in Grothendieck's sense:
--
--   1. $E'_\beta$ has a fundamental sequence of bounded sets: there are bounded sets $B_0, B_1, \dots$ such that every bounded set is contained in some $B_n$ (take the polars $U_n^\circ$ of a countable base of $0$-neighbourhoods of $E$; bounded subsets of $E'_\beta$ are equicontinuous since $E$ is quasi-barrelled);
--   2. if $(U_n)$ is a sequence of closed, balanced, convex $0$-neighbourhoods of $E'_\beta$ whose intersection $\bigcap_n U_n$ absorbs every bounded set, then $\bigcap_n U_n$ is a $0$-neighbourhood.
--
--   This is Schaefer, *Topological Vector Spaces*, IV.8.1 (the strong dual of a metrizable locally convex space is a $(DF)$-space).
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, Lemma C.2.4.11; H. H. Schaefer, Topological Vector Spaces, IV.6.1 (strong dual of bornological space complete), IV.8.1 (strong dual of metrizable LCS is (DF)), IV.9.6 (strong dual of complete nuclear (DF)-space is nuclear)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_frechet_isDF (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    (∃ B : ℕ → Set (StrongDual ℂ E), (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set (StrongDual ℂ E), Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n) ∧
    ∀ U : ℕ → Set (StrongDual ℂ E),
      (∀ n, U n ∈ nhds (0 : StrongDual ℂ E) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set (StrongDual ℂ E), Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : StrongDual ℂ E) := by sorry

end MasulloGRH
