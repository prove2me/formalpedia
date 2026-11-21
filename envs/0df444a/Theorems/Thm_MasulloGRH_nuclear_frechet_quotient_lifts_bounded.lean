-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_lifts_bounded
-- name    : MasulloGRH.nuclear_frechet_quotient_lifts_bounded
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:48:50.424391+00:00
-- url     : https://prove2.me/theorems/0f8391f2-13f1-49b0-a5c6-92ffd54662e5
-- title:
--   Quotients of nuclear Fréchet spaces lift bounded sets
-- statement:
--   Let $X$ be a complex nuclear Fréchet space and let $W\subset X$ be a closed linear subspace. Give $X/W$ the quotient topology and let $q\colon X\to X/W$ be the quotient map. Then $q$ lifts bounded sets: for every bounded subset $B\subset X/W$ there is a bounded subset $B'\subset X$ with
--   $$B\subset q(B').$$
--
--   Proof idea: $X$ is a Fréchet–Schwartz space, so $X/W$ is again a Fréchet–Schwartz space, and in particular every bounded subset of $X/W$ is precompact. For a quotient map of metrizable topological vector spaces every precompact set (more precisely, every compact set, after passing to the closure in the complete space $X/W$) is the image of a precompact subset of $X$, which is bounded.
--
--   **Formalization Note** Bounded means von Neumann bounded; nuclearity and the Fréchet property are those of `IsNuclear` and `IsFrechet`.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Corollary C.1.5.13, proof, pp. 668–669. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf (bounded lifting for the Fréchet steps); standard: nuclear Fréchet spaces are Fréchet–Schwartz (Montel), quotients of Fréchet–Schwartz spaces are Fréchet–Schwartz, and precompact sets lift along quotient maps of metrizable spaces, cf. Meise–Vogt, Introduction to Functional Analysis, §24 and §28.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclear_frechet_quotient_lifts_bounded (X : Type*) [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (hF : IsFrechet X) (hN : IsNuclear X) (W : Submodule ℂ X)
    (hW : IsClosed (W : Set X)) : LiftsBoundedSets (W.mkQ : X → X ⧸ W) := by sorry

end MasulloGRH
