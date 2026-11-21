-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_frechet_bidual_nuclear
-- name    : MasulloGRH.nuclear_of_frechet_bidual_nuclear
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:35:05.282161+00:00
-- url     : https://prove2.me/theorems/09a0a693-875d-451c-bf12-1f2ca0a7f0ec
-- title:
--   A Fréchet space with nuclear strong bidual is nuclear
-- statement:
--   Let $E$ be a Fréchet space over $\mathbb C$ whose strong bidual $E''=(E'_\beta)'_\beta$ is nuclear. Then $E$ is nuclear.
--
--   The reason: a Fréchet space is metrizable and locally convex, hence quasi-barrelled, so the canonical evaluation map $J\colon E\to E''$, $J(x)(f)=f(x)$, is injective (Hahn–Banach) and a topological isomorphism of $E$ onto the subspace $J(E)$ of $E''$ (Schaefer IV.5.6). Subspaces of nuclear spaces are nuclear (Schaefer III.7.3), and nuclearity is invariant under linear topological isomorphisms. This is the second half of the backward direction of Lemma C.2.4.11.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, proof of Lemma C.2.4.11 (Duality and nuclearity for Fréchet spaces), p. 689; classical reference: H. H. Schaefer, Topological Vector Spaces, Ch. III §7.3 and Ch. IV §5.6, §9.6; F. Trèves, Topological Vector Spaces, Distributions and Kernels, Prop. 50.6

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclear_of_frechet_bidual_nuclear (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear (StrongDual ℂ (StrongDual ℂ E))) :
    IsNuclear E := by sorry

end MasulloGRH
