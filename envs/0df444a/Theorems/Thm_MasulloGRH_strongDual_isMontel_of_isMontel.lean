-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_isMontel_of_isMontel
-- name    : MasulloGRH.strongDual_isMontel_of_isMontel
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T09:49:17.230023+00:00
-- url     : https://prove2.me/theorems/44c82a9d-1b71-48a5-a044-a815314bfcde
-- title:
--   The strong dual of a barrelled Montel space is Montel
-- statement:
--   Let $E$ be a complex barrelled space which is **Montel** in the sense of Example C.1.4.6(3): Hausdorff locally convex, every closed bounded subset is compact, and reflexive (the canonical map $E\to(E'_\beta)'_\beta$ is a topological isomorphism).
--
--   Then the strong dual $E'_\beta$ is again Montel.
--
--   This is one of the ingredients of Theorem D.1.5.7 (Main Structure Theorem on Schwartz–Bruhat spaces).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Example C.1.4.6(3), used in the proof of Theorem D.1.5.7, pp. 763–764; Schaefer, Topological Vector Spaces, IV.5.9

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_isMontel_of_isMontel (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hb : BarrelledSpace ℂ E) (hM : IsMontel E) :
    IsMontel (StrongDual ℂ E) := by sorry

end MasulloGRH
