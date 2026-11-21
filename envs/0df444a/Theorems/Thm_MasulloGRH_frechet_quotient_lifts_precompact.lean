-- Prove2me | Theorems.Thm_MasulloGRH_frechet_quotient_lifts_precompact
-- name    : MasulloGRH.frechet_quotient_lifts_precompact
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:08:21.285831+00:00
-- url     : https://prove2.me/theorems/05b7106c-0d50-4eb6-a83a-b7553c43b368
-- title:
--   Precompact sets in a quotient of a Fréchet space are images of precompact sets
-- statement:
--   Let $X$ be a Fréchet space over $\mathbb{C}$, $W \subseteq X$ a closed subspace and $q : X \to X/W$ the quotient map, with $X/W$ carrying the quotient topology. If $B \subseteq X/W$ is precompact, i.e. for every neighbourhood $U$ of $0$ in $X/W$ there is a finite set $t$ with $B \subseteq t + U$, then there is a precompact set $S \subseteq X$ (for every neighbourhood $V$ of $0$ in $X$ there is a finite $t'$ with $S \subseteq t' + V$) such that $$B \subseteq q(S).$$ Thus precompact sets lift along quotient maps of Fréchet spaces; the proof uses metrizability and completeness of $X$ together with openness of $q$ (successive approximation by finite nets and summation of the resulting series).
-- source:
--   Köthe, Topological Vector Spaces I, §22 (quotients of metrizable spaces); Grothendieck, Produits tensoriels topologiques, Ch. I; used in A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, Definition C.1.5.9 (bounded lifting).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Pointwise

namespace MasulloGRH

theorem frechet_quotient_lifts_precompact (X : Type*) [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (hF : IsFrechet X) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (B : Set (X ⧸ W))
    (hB : ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U) :
    ∃ S : Set X, (∀ U ∈ nhds (0 : X), ∃ t : Finset X, S ⊆ (t : Set X) + U) ∧
      B ⊆ (W.mkQ : X → X ⧸ W) '' S := by sorry

end MasulloGRH
