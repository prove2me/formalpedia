-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional
-- name    : IsDiscreteValuationRing.exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/dfad8cce-87ca-593f-b068-6812eb277216
-- title:
--   A discrete valuation subring of A with fraction field K'
-- statement:
--   Let $O$ be a discrete valuation ring which is a domain, let $F$ be a field that is a fraction field of $O$, let $L$ be a field, let $A$ be a valuation subring of $L$ and $K'$ a subfield of $L$. Assume $K'$ carries compatible $O$- and $F$-algebra structures (a scalar tower over $O \to F \to K'$), and that $K'$ is finite-dimensional and separable over $F$. Let $\iota_A \colon O \to A$ be a ring homomorphism which is local (it maps non-units to non-units), and assume that for every $x \in O$ the image $\iota_A(x)$, viewed in $L$, equals the image in $L$ of the structure map value $\mathrm{algebraMap}_{O,K'}(x)$. The conclusion asserts the existence of a type $O'$ with a commutative ring structure making it a domain and a discrete valuation ring, together with ring homomorphisms $\sigma \colon O \to O'$, $\iota' \colon O' \to A$ and $j' \colon O' \to K'$ such that: $\iota'$ is injective and local; $\sigma$ followed by $\iota'$ equals $\iota_A$; $\iota'$ and $j'$ agree after composing with the inclusions into $L$; $\sigma$ followed by $j'$ equals the structure map $O \to K'$; and every $c \in K'$ can be written as $j'(a)/j'(b)$ with $a,b \in O'$ and $j'(b) \neq 0$, so that $j'$ exhibits $K'$ as a fraction field of $O'$.
--
--   This produces a discrete valuation coefficient ring $O'$ intermediate between $O$ and the valuation ring $A$, with fraction field the prescribed finite separable extension $K'$ of $F$ inside $L$: concretely a localisation of the integral closure of $O$ in $K'$ at the prime cut out by the maximal ideal of $A$. It is used in the construction of models of modular curves over discrete valuation rings, where enlarging the coefficient ring by finitely many algebraic elements at a place is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsDiscreteValuationRing.exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
    {L : Type} [Field L] (A : ValuationSubring L) (K' : Subfield L)
    [Algebra O K'] [Algebra F K'] [IsScalarTower O F K'] [FiniteDimensional F K'] [Algebra.IsSeparable F K']
    (ιA : O →+* A) [IsLocalHom ιA] (hιA : ∀ x : O, ((ιA x : A) : L) = ((algebraMap O K' x : K') : L)) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (σ : O →+* O') (ι' : O' →+* A) (j' : O' →+* K'),
      Function.Injective ι' ∧ IsLocalHom ι' ∧ ι'.comp σ = ιA ∧
      (∀ x : O', ((ι' x : A) : L) = ((j' x : K') : L)) ∧ j'.comp σ = algebraMap O K' ∧
      (∀ c : K', ∃ a b : O', j' b ≠ 0 ∧ c * j' b = j' a) := by sorry
