-- Prove2me | Theorems.Thm_MasulloGRH_bounded_iff_weakly_bounded
-- name    : MasulloGRH.bounded_iff_weakly_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T21:48:58.972587+00:00
-- url     : https://prove2.me/theorems/2623da9b-a089-4b0c-96e4-af9375b82e0c
-- title:
--   Proposition C.1.4.1 — a subset of a Hausdorff locally convex space is bounded iff it is weakly bounded
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ and $B\subset E$ a subset. Then $B$ is bounded in $E$, i.e. absorbed by every neighbourhood of $0$, if and only if $\ell(B)$ is a bounded subset of $\mathbb C$ for every continuous linear functional $\ell$ on $E$.
--
--   This is Mackey's theorem on bounded sets. It allows boundedness in the function spaces of the draft to be tested against continuous functionals.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.1.4, Proposition C.1.4.1, p. 661

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem bounded_iff_weakly_bounded (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) (B : Set E) :
    Bornology.IsVonNBounded ℂ B ↔ ∀ ℓ : StrongDual ℂ E, Bornology.IsBounded (ℓ '' B) := by sorry

end MasulloGRH
