-- Prove2me | Theorems.Thm_MasulloGRH_bidual_nuclear_of_frechet_strong_dual_nuclear
-- name    : MasulloGRH.bidual_nuclear_of_frechet_strong_dual_nuclear
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:35:04.900622+00:00
-- url     : https://prove2.me/theorems/cfb5b55b-da05-4e6b-9c07-d1ebfa995b0c
-- title:
--   If the strong dual of a Fréchet space is nuclear, so is its strong bidual
-- statement:
--   Let $E$ be a Fréchet space over $\mathbb C$ whose strong dual $E'_\beta$ is nuclear. Then the strong bidual $(E'_\beta)'_\beta$ is nuclear.
--
--   The reason: the strong dual of a Fréchet space is a complete $(DF)$-space, and the strong dual of a complete nuclear $(DF)$-space is a nuclear (Fréchet) space (Schaefer, *Topological Vector Spaces*, IV.9.6). This is the first half of the backward direction of Lemma C.2.4.11.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, proof of Lemma C.2.4.11 (Duality and nuclearity for Fréchet spaces), p. 689; classical reference: H. H. Schaefer, Topological Vector Spaces, Ch. III §7.3 and Ch. IV §5.6, §9.6; F. Trèves, Topological Vector Spaces, Distributions and Kernels, Prop. 50.6

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem bidual_nuclear_of_frechet_strong_dual_nuclear (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear (StrongDual ℂ E)) :
    IsNuclear (StrongDual ℂ (StrongDual ℂ E)) := by sorry

end MasulloGRH
