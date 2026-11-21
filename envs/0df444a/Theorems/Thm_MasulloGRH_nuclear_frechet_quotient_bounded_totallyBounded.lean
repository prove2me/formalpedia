-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_bounded_totallyBounded
-- name    : MasulloGRH.nuclear_frechet_quotient_bounded_totallyBounded
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:57:34.630565+00:00
-- url     : https://prove2.me/theorems/845ccedf-89b7-4fd4-88be-1ce2ebd42d4d
-- title:
--   Bounded sets in a quotient of a nuclear Fréchet space are precompact
-- statement:
--   Let $X$ be a nuclear Fréchet space over $\mathbb{C}$ and $W \subseteq X$ a closed subspace, and give $X/W$ the quotient topology. Then every (von Neumann) bounded subset $B \subseteq X/W$ is precompact (totally bounded): for every neighbourhood $U$ of $0$ in $X/W$ there is a finite set $t \subseteq X/W$ with $$B \subseteq t + U.$$ This holds because $X/W$ is again a nuclear Fréchet space, and nuclear spaces are Schwartz spaces, in which bounded sets are precompact (equivalently, nuclear Fréchet spaces are Montel).
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, §C.1.4 (Example C.1.4.6: nuclear Fréchet spaces are Montel) and Definition C.1.5.9 (bounded lifting); standard: Köthe, Topological Vector Spaces I, §27–28; Grothendieck, Produits tensoriels topologiques, Ch. II.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Pointwise

namespace MasulloGRH

theorem nuclear_frechet_quotient_bounded_totallyBounded (X : Type*) [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] (hF : IsFrechet X) (hN : IsNuclear X)
    (W : Submodule ℂ X) (hW : IsClosed (W : Set X)) (B : Set (X ⧸ W))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U := by sorry

end MasulloGRH
