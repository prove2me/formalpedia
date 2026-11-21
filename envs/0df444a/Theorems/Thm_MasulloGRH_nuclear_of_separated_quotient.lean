-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_separated_quotient
-- name    : MasulloGRH.nuclear_of_separated_quotient
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:39:17.868425+00:00
-- url     : https://prove2.me/theorems/03023b64-db58-4ad7-8c39-98874430e7f5
-- title:
--   A Hausdorff quotient of a nuclear space is nuclear
-- statement:
--   Let $G$ be a nuclear space over $\mathbb C$ and let $q : G \to E$ be a surjective linear map onto a complex vector space $E$. Suppose $E$ carries the finest locally convex topology for which $q$ is continuous (equivalently, $E$ is the quotient $G/\ker q$ with the quotient topology), and that this topology is Hausdorff. Then $E$ is nuclear.
--
--   Here nuclearity is in the sense of Definition C.2.4.1: $E$ is a Hausdorff locally convex space and for every Hausdorff locally convex space $F$ the projective and injective topologies on $E \otimes F$ coincide.
--
--   This is the classical permanence property "a separated quotient of a nuclear space is nuclear" (Schaefer, *Topological Vector Spaces*, III.7.3, Corollary; Trèves, *Topological Vector Spaces, Distributions and Kernels*, Proposition 50.1).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, Lemma C.2.4.12(1), p. 689 (proof step); classical references: H. H. Schaefer, Topological Vector Spaces, Ch. III, §7.3 Corollary; F. Trèves, Topological Vector Spaces, Distributions and Kernels, Prop. 50.1.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclear_of_separated_quotient (G E : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hG : IsNuclear G) (hE : IsHLCS E) (q : G →ₗ[ℂ] E) (hq : Function.Surjective q)
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ @Continuous G E _ t q}) :
    IsNuclear E := by sorry

end MasulloGRH
