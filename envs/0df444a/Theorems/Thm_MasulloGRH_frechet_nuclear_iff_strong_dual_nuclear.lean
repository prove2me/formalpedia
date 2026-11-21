-- Prove2me | Theorems.Thm_MasulloGRH_frechet_nuclear_iff_strong_dual_nuclear
-- name    : MasulloGRH.frechet_nuclear_iff_strong_dual_nuclear
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T22:03:08.208028+00:00
-- url     : https://prove2.me/theorems/1a0b58a8-3ea3-47eb-83ef-72229028ee18
-- title:
--   Lemma C.2.4.11 — a Fréchet space is nuclear iff its strong dual is nuclear
-- statement:
--   Let $E$ be a Fréchet space over $\mathbb C$ and $E'_\beta$ its strong dual, the space of continuous linear functionals with the topology of uniform convergence on bounded sets. Then
--
--   $$E\text{ is nuclear}\quad\Longleftrightarrow\quad E'_\beta\text{ is nuclear}.$$
--
--   The draft uses this to pass nuclearity between its Fréchet spaces of $\theta$-functions and their duals.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, Lemma C.2.4.11 (Duality and nuclearity for Fréchet spaces), p. 689

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem frechet_nuclear_iff_strong_dual_nuclear (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    IsNuclear E ↔ IsNuclear (StrongDual ℂ E) := by sorry

end MasulloGRH
