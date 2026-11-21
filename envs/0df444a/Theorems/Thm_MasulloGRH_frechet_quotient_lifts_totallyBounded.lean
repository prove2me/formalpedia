-- Prove2me | Theorems.Thm_MasulloGRH_frechet_quotient_lifts_totallyBounded
-- name    : MasulloGRH.frechet_quotient_lifts_totallyBounded
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T22:57:32.381014+00:00
-- url     : https://prove2.me/theorems/bdc0b41f-be76-480c-a2b5-b28eca1537fe
-- title:
--   Precompact sets lift along quotients of Fréchet spaces
-- statement:
--   Let $X$ be a Fréchet space over $\mathbb{C}$, $W \subseteq X$ a closed subspace and $q : X \to X/W$ the quotient map. If $B \subseteq X/W$ is precompact, i.e. for every neighbourhood $U$ of $0$ in $X/W$ there is a finite $t$ with $B \subseteq t + U$, then there is a bounded set $B' \subseteq X$ with $$B \subseteq q(B').$$ Classically: in the metrizable complete space $X/W$ a precompact set lies in the closed absolutely convex hull $\{\sum \lambda_n x_n : \sum |\lambda_n| \le 1\}$ of a null sequence $(x_n)$; lift $(x_n)$ to a null sequence $(y_n)$ in $X$ using openness of $q$ and metrizability, and take $B' = \{\sum \lambda_n y_n : \sum|\lambda_n| \le 1\}$, which is bounded and well defined by completeness of $X$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, §C.1.4 (Example C.1.4.6: nuclear Fréchet spaces are Montel) and Definition C.1.5.9 (bounded lifting); standard: Köthe, Topological Vector Spaces I, §27–28; Grothendieck, Produits tensoriels topologiques, Ch. II.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Pointwise

namespace MasulloGRH

theorem frechet_quotient_lifts_totallyBounded (X : Type*) [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (hF : IsFrechet X) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (B : Set (X ⧸ W))
    (hB : ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U) :
    ∃ B' : Set X, Bornology.IsVonNBounded ℂ B' ∧ B ⊆ (W.mkQ : X → X ⧸ W) '' B' := by sorry

end MasulloGRH
