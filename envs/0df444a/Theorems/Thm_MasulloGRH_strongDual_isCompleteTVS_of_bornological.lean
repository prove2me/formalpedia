-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_isCompleteTVS_of_bornological
-- name    : MasulloGRH.strongDual_isCompleteTVS_of_bornological
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T09:48:59.011597+00:00
-- url     : https://prove2.me/theorems/63b6a0a0-a61f-43fc-bf49-7e6c895e57c5
-- title:
--   The strong dual of a bornological space is complete
-- statement:
--   Let $E$ be a complex Hausdorff locally convex space which is **bornological** (every seminorm bounded on bounded sets is continuous).
--
--   Then its strong dual $E'_\beta$ is **complete**: it is Hausdorff and every Cauchy filter converges.
--
--   This is one of the ingredients of Theorem D.1.5.7 (Main Structure Theorem on Schwartz–Bruhat spaces).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.1.4 (strong duals of bornological spaces are complete), used in the proof of Theorem D.1.5.7, pp. 763–764; Schaefer, Topological Vector Spaces, IV.6.1 Cor. 1

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_isCompleteTVS_of_bornological (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) (hb : IsBornological E) :
    IsCompleteTVS (StrongDual ℂ E) := by sorry

end MasulloGRH
