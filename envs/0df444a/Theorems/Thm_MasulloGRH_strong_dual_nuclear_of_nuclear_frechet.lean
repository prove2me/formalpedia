-- Prove2me | Theorems.Thm_MasulloGRH_strong_dual_nuclear_of_nuclear_frechet
-- name    : MasulloGRH.strong_dual_nuclear_of_nuclear_frechet
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:35:06.582976+00:00
-- url     : https://prove2.me/theorems/26382012-6e1d-4f8e-8905-1cf4b7b99706
-- title:
--   The strong dual of a nuclear Fréchet space is nuclear
-- statement:
--   Let $E$ be a Fréchet space over $\mathbb C$ which is nuclear, i.e. the projective and injective topologies on $E\otimes F$ coincide for every Hausdorff locally convex space $F$. Then its strong dual $E'_\beta$ (continuous linear functionals with the topology of uniform convergence on bounded subsets of $E$) is nuclear:
--
--   $$E \text{ Fréchet and nuclear} \;\Longrightarrow\; E'_\beta \text{ nuclear}.$$
--
--   This is the forward direction of Lemma C.2.4.11 (Schaefer, *Topological Vector Spaces*, IV.9.6).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, proof of Lemma C.2.4.11 (Duality and nuclearity for Fréchet spaces), p. 689; classical reference: H. H. Schaefer, Topological Vector Spaces, Ch. III §7.3 and Ch. IV §5.6, §9.6; F. Trèves, Topological Vector Spaces, Distributions and Kernels, Prop. 50.6

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strong_dual_nuclear_of_nuclear_frechet (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E) :
    IsNuclear (StrongDual ℂ E) := by sorry

end MasulloGRH
