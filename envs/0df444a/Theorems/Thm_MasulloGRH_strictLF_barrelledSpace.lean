-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_barrelledSpace
-- name    : MasulloGRH.strictLF_barrelledSpace
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T09:48:57.334686+00:00
-- url     : https://prove2.me/theorems/894ffe12-e5dc-4f4d-82f9-cbe6c9431884
-- title:
--   Strict LF-spaces are barrelled
-- statement:
--   Let $E$ be a complex strict LF-space: $E=\bigcup_n X_n$ for an increasing sequence of subspaces $X_n$, each a Fréchet space in the topology induced from $E$, and $E$ carries the finest locally convex topology making all inclusions $X_n\hookrightarrow E$ continuous.
--
--   Then $E$ is **barrelled** (in Mathlib's sense `BarrelledSpace ℂ E`): every lower semicontinuous seminorm on $E$ is continuous.
--
--   This is one of the ingredients of Theorem D.1.5.7 (Main Structure Theorem on Schwartz–Bruhat spaces).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.1.4–C.1.5 (LF-spaces are barrelled), used in the proof of Theorem D.1.5.7, pp. 763–764

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_barrelledSpace (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsStrictLF E) : BarrelledSpace ℂ E := by sorry

end MasulloGRH
