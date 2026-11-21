-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_countable_directSum
-- name    : MasulloGRH.nuclear_countable_directSum
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:39:12.205161+00:00
-- url     : https://prove2.me/theorems/a5346770-a2db-4f11-a578-adcb0500325f
-- title:
--   The locally convex direct sum of countably many nuclear spaces is nuclear
-- statement:
--   Let $(Y_n)_{n \in \mathbb N}$ be a sequence of nuclear spaces over $\mathbb C$ and let $\bigoplus_n Y_n$ be their algebraic direct sum, equipped with the locally convex direct sum topology: the finest locally convex topology for which every canonical injection $Y_n \to \bigoplus_n Y_n$ is continuous. Then $\bigoplus_n Y_n$ is nuclear (in particular Hausdorff).
--
--   Nuclearity is in the sense of Definition C.2.4.1: Hausdorff locally convex, and for every Hausdorff locally convex space $F$ the projective and injective topologies on the tensor product with $F$ coincide.
--
--   This is the classical permanence property of nuclear spaces under countable locally convex direct sums (Schaefer, *Topological Vector Spaces*, III.7.4; Trèves, *Topological Vector Spaces, Distributions and Kernels*, Proposition 50.1).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, Lemma C.2.4.12(1), p. 689 (proof step); classical references: H. H. Schaefer, Topological Vector Spaces, Ch. III, §7.4; F. Trèves, Topological Vector Spaces, Distributions and Kernels, Prop. 50.1.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclear_countable_directSum (Y : ℕ → Type*) [∀ n, AddCommGroup (Y n)]
    [∀ n, Module ℂ (Y n)] (τ : ∀ n, TopologicalSpace (Y n))
    (hY : ∀ n, @IsNuclear (Y n) _ _ (τ n))
    (t : TopologicalSpace (DirectSum ℕ Y))
    (ht : t = sInf {t' | IsLocallyConvexTopology (DirectSum ℕ Y) t' ∧
      ∀ n, @Continuous (Y n) (DirectSum ℕ Y) (τ n) t' (DirectSum.lof ℂ ℕ Y n)}) :
    @IsNuclear (DirectSum ℕ Y) _ _ t := by sorry

end MasulloGRH
