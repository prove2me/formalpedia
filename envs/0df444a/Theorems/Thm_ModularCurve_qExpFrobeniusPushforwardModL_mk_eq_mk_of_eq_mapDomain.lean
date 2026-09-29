-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain
-- name    : ModularCurve.qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/a1390273-50cf-59c2-ad7b-a4407c84bd28
-- title:
--   Frobenius push-forward on Pic⁰ computed by Φ_* on divisors
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$, and write $\bar F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the ratios of $K$-reductions of integral $q$-expansions of modular forms of level $\Gamma$. Assume `hx`: there is $x \in \bar F$ transcendental over $K$ with $\bar F$ finite-dimensional over $K(x)$. Let $F$ be an additive endomorphism of $\mathrm{Pic}^0 =$ `Pic0 K \bar F`, the quotient of the degree-zero divisors (the kernel of the degree homomorphism on the finitely supported $\mathbb Z$-valued functions on the places `Place K \bar F`) by the subgroup of principal divisors, and assume $F$ agrees pointwise with [`ModularCurve.qExpFrobeniusPushforwardModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L243) (the push-forward map on $\mathrm{Pic}^0$ attached to the Frobenius $K$-algebra endomorphism $q \mapsto q^p$ of $\bar F$ when the inputs `QExpFrobeniusInputsModL` hold, and $0$ otherwise). Let $\Phi$ be a self-bijection of the set of places of $\bar F$ over $K$ agreeing pointwise with [`ModularCurve.qExpFrobeniusPlaceModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L132), the restriction of a place along that Frobenius. The conclusion: for all degree-zero divisors $D, D'$ whose underlying divisors satisfy $D' = \Phi_* D$ (`Finsupp.mapDomain`), one has $F([D]) = [D']$ in $\mathrm{Pic}^0$.
--
--   This identifies the Frobenius push-forward on the degree-zero divisor class group of the $q$-expansion function field with the map induced by the Frobenius permutation of places, in the form in which it is consumed downstream. It is used as the divisor-level input in the study of the Hecke operator $U_p$ and of the Frobenius action on Tate modules of Jacobians of modular curves in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hx : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ))
    (F : Pic0 K (ModularCurve.qExpFunctionFieldC K Γ) →+ Pic0 K (ModularCurve.qExpFunctionFieldC K Γ))
    (hF : ∀ z, F z = ModularCurve.qExpFrobeniusPushforwardModL K Γ p z)
    (Φ : Place K (ModularCurve.qExpFunctionFieldC K Γ) ≃ Place K (ModularCurve.qExpFunctionFieldC K Γ))
    (hΦ : ∀ v, Φ v = ModularCurve.qExpFrobeniusPlaceModL K Γ p v) :
    ∀ (D D' : Divisor.degZero (K := K) (F := ModularCurve.qExpFunctionFieldC K Γ)),
      (D' : Divisor K (ModularCurve.qExpFunctionFieldC K Γ)) =
        Finsupp.mapDomain Φ (D : Divisor K (ModularCurve.qExpFunctionFieldC K Γ)) →
      F (Pic0.mk D) = Pic0.mk D' := by sorry
