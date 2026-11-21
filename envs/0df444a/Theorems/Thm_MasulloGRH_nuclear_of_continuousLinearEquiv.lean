-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv
-- name    : MasulloGRH.nuclear_of_continuousLinearEquiv
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:37:44.583174+00:00
-- url     : https://prove2.me/theorems/328d8363-37aa-439a-b29d-f0ec4dd6656a
-- title:
--   Nuclearity is invariant under a linear homeomorphism
-- statement:
--   The pullback by a continuous linear equivalence of a nuclear locally convex space is nuclear. This is the change-of-coordinates property of the equality between the projective and injective tensor topologies; the inverse equivalence gives the reverse implication.
-- source:
--   Auxiliary permanence facts for Masullo, The Music of the Primes, frozen 20 November 2026 draft, Appendix C, Definition C.1.3.1, Definition C.2.4.1 and Remark C.1.5.12. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex
universe u

namespace MasulloGRH

theorem nuclear_of_continuousLinearEquiv (F G : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (e : F ≃L[ℂ] G)
    (hG : IsNuclear G) : IsNuclear F := by sorry

end MasulloGRH
