-- Prove2me | Theorems.Thm_MazurTransfer_surjective_of_finite_quotient_of_injective
-- name    : MazurTransfer.surjective_of_finite_quotient_of_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T11:31:14.611583+00:00
-- url     : https://prove2.me/theorems/5cbdcaf4-bf71-40e8-ad22-43dd2ad226ca
-- title:
--   Surjectivity from a finite-index stable subgroup
-- statement:
--   Let $A$ be a commutative group, let $f:A\to A$ be an injective endomorphism, and let $U\le A$ have finite index. Suppose that $f(U)\subseteq U$ and that the restriction $f:U\to U$ is surjective. Then $f:A\to A$ is surjective. This criterion separates the finite quotient of a local group from a subgroup on which an endomorphism can be inverted directly.
-- source:
--   Original elementary group-theoretic proof developed for the MazurTheorem integration, https://github.com/Vilin97/MazurTheorem. The checked local consumer is MazurTransfer.Order13ActualPiThirteenLocalNormReduction.original_localPi_surjective_of_formal_subgroup. The finite-index subgroup in the arithmetic application remains to be constructed.

import Mathlib

theorem MazurTransfer.surjective_of_finite_quotient_of_injective (A : Type) [CommGroup A] (f : A →* A) (U : Subgroup A)
    [Finite (A ⧸ U)] (hU : U ≤ U.comap f)
    (hs : ∀ u ∈ U, ∃ v ∈ U, f v = u)
    (hi : Function.Injective f) : Function.Surjective f := by sorry
