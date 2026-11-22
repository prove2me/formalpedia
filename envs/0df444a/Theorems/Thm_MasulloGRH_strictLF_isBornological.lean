-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_isBornological
-- name    : MasulloGRH.strictLF_isBornological
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T09:48:59.642605+00:00
-- url     : https://prove2.me/theorems/69406a4e-a7af-48b2-8054-ba4f07aac488
-- title:
--   Strict LF-spaces are bornological
-- statement:
--   Let $E$ be a complex strict LF-space ($E=\bigcup_n X_n$, increasing steps that are Fréchet in the induced topology, with the locally convex inductive limit topology).
--
--   Then $E$ is **bornological**: every seminorm on $E$ that is bounded on each von Neumann bounded subset of $E$ is continuous.
--
--   This is one of the ingredients of Theorem D.1.5.7 (Main Structure Theorem on Schwartz–Bruhat spaces).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.1.4–C.1.5 (LF-spaces are bornological), used in the proof of Theorem D.1.5.7, pp. 763–764

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_isBornological (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsStrictLF E) : IsBornological E := by sorry

end MasulloGRH
