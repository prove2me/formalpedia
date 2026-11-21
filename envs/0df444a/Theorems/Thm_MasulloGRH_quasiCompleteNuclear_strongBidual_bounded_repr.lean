-- Prove2me | Theorems.Thm_MasulloGRH_quasiCompleteNuclear_strongBidual_bounded_repr
-- name    : MasulloGRH.quasiCompleteNuclear_strongBidual_bounded_repr
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:53:38.682611+00:00
-- url     : https://prove2.me/theorems/d589ecc2-f765-4cab-a8f3-c7e6258d5575
-- title:
--   Bounded bidual representation for quasi-complete nuclear spaces
-- statement:
--   Let $E$ be a quasi-complete nuclear complex locally convex space, and let $q$ be a continuous seminorm on its strong dual $E'_\beta$. There is a bounded set $D\subseteq E$ such that every continuous linear functional $F$ on $E'_\beta$ satisfying $|F(f)|\le q(f)$ for all $f\in E'$ is evaluation at a point of $D$:
--
--   $$\forall F\in(E'_\beta)',\quad |F|\le q\ \Longrightarrow\ \exists y\in D,\ \forall f\in E',\ F(f)=f(y).$$
--
--   In particular, every element of the strong bidual is represented by a point of $E$. The uniform boundedness of the representing set is part of the conclusion. Quasi-completeness means every bounded Cauchy filter converges.
--
--   This strengthens the mission's corresponding nuclear Fréchet representation theorem: metrizability is removed, and completeness is replaced by quasi-completeness. No equality between the original topology and the strong bidual topology is asserted here.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Appendix C, Lemma C.2.4.16(1) and following remark, p. 690, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf: bounded sets in a nuclear space are precompact, and under quasi-completeness have compact closure (citing Trèves, Corollary 1 to Proposition 50.2). The bounded-representation assertion is derived here from that compactness consequence and the compact-disk representation principle. It strengthens https://prove2.me/theorems/50be0b68-d0e6-4278-8467-1e159a61668e without claiming canonical topological reflexivity.

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Topology Filter Set
open scoped ComplexOrder Pointwise

theorem MasulloGRH.quasiCompleteNuclear_strongBidual_bounded_repr (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsQuasiComplete E) (hN : IsNuclear E)
    (q : Seminorm ℂ (StrongDual ℂ E)) (hq : Continuous q) :
    ∃ D : Set E, Bornology.IsVonNBounded ℂ D ∧
      ∀ F : StrongDual ℂ (StrongDual ℂ E), (∀ f, ‖F f‖ ≤ q f) →
        ∃ y ∈ D, ∀ f : StrongDual ℂ E, F f = f y := by sorry
