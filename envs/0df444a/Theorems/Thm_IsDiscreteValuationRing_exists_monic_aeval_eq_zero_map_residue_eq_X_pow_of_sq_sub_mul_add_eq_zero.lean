-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero
-- name    : IsDiscreteValuationRing.exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/09873350-946e-5bc0-b503-54de7779edfe
-- title:
--   Residual vanishing of roots of X²-aX+varpi
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring which is a commutative domain, let $F$ be a field equipped with an $\mathcal{O}$-algebra structure whose structure map is injective, let $\varpi$ be an element of the maximal ideal of $\mathcal{O}$, and let $a,x \in F$. Call an element $y$ of $F$ *residually zero* if there is a monic $R \in \mathcal{O}[X]$ with $R(y)=0$ (the evaluation taken through the algebra map) whose reduction along the residue map $\mathcal{O} \to \mathcal{O}/\mathfrak{m}$ equals $(X - C\,0)^{\deg R}$, that is $X^{\deg R}$, in the residue field's polynomial ring. The hypotheses are that $a$ is residually zero in this sense and that $x$ satisfies the quadratic relation $x \cdot x - a x + \varpi = 0$ in $F$, where $\varpi$ is viewed in $F$ through the algebra map. The conclusion is that $x$ is residually zero: there exists a monic $p \in \mathcal{O}[X]$ with $p(x)=0$ and $p$ reducing to $X^{\deg p}$ modulo $\mathfrak{m}$.
--
--   The predicate used here is a polynomial substitute for the congruence "$y \equiv 0$ modulo the maximal ideal" which makes sense in an $\mathcal{O}$-algebra, such as an algebraic closure of the fraction field, carrying no residue map; the result says that a root of a quadratic $X^2 - aX + \varpi$ with residually zero $a$ and $\varpi$ in the maximal ideal is again residually zero. It serves the local computation at a prime exactly dividing the level where the residual representation is not ordinary, being used in the count of residually vanishing Frobenius roots in [`CuspForm.heckeLocal.sum_rootMultiplicity_residual_eq_two_of_not_isOrdinaryAt`](thm.html#CuspForm.heckeLocal.sum_rootMultiplicity_residual_eq_two_of_not_isOrdinaryAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero.lean

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsDiscreteValuationRing.exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {F : Type} [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (ϖ : 𝒪) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal 𝒪) (a x : F)
    (ha : (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval a R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C 0) ^ R.natDegree))
    (hx : x * x - a * x + algebraMap 𝒪 F ϖ = 0) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C 0) ^ R.natDegree) := by sorry
