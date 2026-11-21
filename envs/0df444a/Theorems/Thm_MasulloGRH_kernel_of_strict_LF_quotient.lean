-- Prove2me | Theorems.Thm_MasulloGRH_kernel_of_strict_LF_quotient
-- name    : MasulloGRH.kernel_of_strict_LF_quotient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T21:58:25.628688+00:00
-- url     : https://prove2.me/theorems/4b0a958f-6d5a-4c96-a9e1-73cebb3cf7e1
-- title:
--   Corollary C.1.5.13 — if $E$ and $E/F$ are strict inductive limits of nuclear Fréchet spaces, so is $F$
-- statement:
--   Let $E$ be a strict locally convex inductive limit of a sequence of nuclear Fréchet spaces and $F\subset E$ a closed linear subspace such that the quotient $E/F$, with the quotient topology, is also a strict locally convex inductive limit of a sequence of nuclear Fréchet spaces. Then:
--
--   1. the quotient map $q\colon E\to E/F$ lifts bounded subsets: every bounded subset of $E/F$ is contained in the image of a bounded subset of $E$;
--   2. $F=\ker(q)$, with the topology induced by $E$, is a strict locally convex inductive limit of a sequence of nuclear Fréchet spaces.
--
--   The draft applies this to the kernels of the operators $\Phi_F$ and $\Phi_{F,S}$ on Schwartz–Bruhat spaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.1.5, Corollary C.1.5.13, p. 668

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem kernel_of_strict_LF_quotient (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsStrictLFOfNuclearFrechet E)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) (hQ : IsStrictLFOfNuclearFrechet (E ⧸ V)) :
    LiftsBoundedSets (V.mkQ : E → E ⧸ V) ∧ IsStrictLFOfNuclearFrechet V := by sorry

end MasulloGRH
