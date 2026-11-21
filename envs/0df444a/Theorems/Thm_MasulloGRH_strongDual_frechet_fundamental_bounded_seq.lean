-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_frechet_fundamental_bounded_seq
-- name    : MasulloGRH.strongDual_frechet_fundamental_bounded_seq
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:27:09.332159+00:00
-- url     : https://prove2.me/theorems/485214a9-dff9-4e38-b925-74506bde2a02
-- title:
--   The strong dual of a Fréchet space has a fundamental sequence of bounded sets
-- statement:
--   Let $E$ be a Fréchet space over $\mathbb C$ and $E'_\beta$ its strong dual (continuous linear functionals, topology of uniform convergence on bounded subsets of $E$). Then $E'_\beta$ has a **fundamental sequence of bounded sets**: there are bounded sets $B_0, B_1, B_2, \dots \subseteq E'_\beta$ such that
--
--   $$\text{every bounded } S \subseteq E'_\beta \text{ satisfies } S \subseteq B_n \text{ for some } n.$$
--
--   One may take $B_n = U_n^\circ$, the polars of a countable base $(U_n)$ of $0$-neighbourhoods of $E$: equicontinuous sets are strongly bounded, and since $E$ is barrelled (Baire), strongly bounded sets are equicontinuous. This is the first half of the $(DF)$ property of $E'_\beta$.
-- source:
--   H. H. Schaefer, Topological Vector Spaces, IV.8.1 and its proof (the strong dual of a metrizable locally convex space is a (DF)-space); A. Grothendieck, Sur les espaces (F) et (DF), Summa Brasil. Math. 3 (1954); used in A. M. Masullo, The Music of the Primes (draft), Appendix C, Lemma C.2.4.11

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_frechet_fundamental_bounded_seq (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    ∃ B : ℕ → Set (StrongDual ℂ E), (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set (StrongDual ℂ E), Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n := by sorry

end MasulloGRH
