-- Prove2me | Theorems.Thm_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
-- name    : Ideal.isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/eb088130-fecd-507f-b669-48fdbdf275d3
-- title:
--   Reducedness of A/(x) from uniformisers at associated primes
-- statement:
--   Let $A$ be a commutative Noetherian ring and let $x \in A$. Assume that for every prime ideal $P$ of $A$ which belongs to $\operatorname{Ass}_A(A/xA)$, the set of associated primes of the $A$-module $A \,/\, \operatorname{span}\{x\}$, the image of the ideal $\operatorname{span}\{x\}$ under the structure map $A \to A_P$ generates the maximal ideal of the local ring $A_P =$ `Localization.AtPrime P`; that is, $x A_P = \mathfrak{m}_{A_P}$. The conclusion is that the quotient ring $A \,/\, \operatorname{span}\{x\}$ is reduced, i.e. its only nilpotent element is $0$.
--
--   This is the standard criterion showing that a principal quotient of a Noetherian ring is reduced as soon as $x$ is a uniformiser in each localisation at an associated prime of $A/xA$. It is used in the project to derive the corresponding statement for integrally closed rings, where the hypothesis is checked only at the minimal primes of $xA$, via [`IsIntegrallyClosed.isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes`](thm.html#IsIntegrallyClosed.isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ideal.isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A] (x : A)
    (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ associatedPrimes A (A ⧸ Ideal.span {x}) →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    IsReduced (A ⧸ Ideal.span {x}) := by sorry
