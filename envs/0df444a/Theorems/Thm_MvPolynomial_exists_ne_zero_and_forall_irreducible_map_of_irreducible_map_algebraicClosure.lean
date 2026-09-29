-- Prove2me | Theorems.Thm_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
-- name    : MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/1c289688-3956-5793-9dd3-01975d3c6e80
-- title:
--   Bertini–Noether: absolute irreducibility spreads out
-- statement:
--   Let $R$ be a commutative ring that is a domain, let $\sigma$ be a finite index type for the variables, and let $F \in R[X_i : i \in \sigma]$ be a multivariate polynomial. Write $K = \operatorname{Frac}(R)$ for the fraction field of $R$ and $\overline{K}$ for its algebraic closure, and assume that the image of $F$ under the coefficientwise map $R \to \overline{K}$ induced by the structure map of $\overline{K}$ as an $R$-algebra is irreducible as an element of $\overline{K}[X_i : i \in \sigma]$, i.e. $F$ is absolutely irreducible over $K$. The conclusion is that there exists $c \in R$ with $c \neq 0$ such that for every field $E$ and every ring homomorphism $\varphi \colon R \to E$ with $\varphi(c) \neq 0$, the polynomial $\varphi(F) \in E[X_i : i \in \sigma]$ obtained by applying $\varphi$ to the coefficients of $F$ is irreducible. The element $c$ depends only on $F$ and is chosen before the field $E$ and the homomorphism $\varphi$; since $E$ ranges over all fields, the conclusion applies in particular to extensions of a residue field of $R$, so the specialisations of $F$ away from $c$ are again absolutely irreducible.
--
--   This is the theorem of Bertini–Noether on the permanence of absolute irreducibility of a hypersurface under specialisation of the coefficients: absolute irreducibility of $F$ at the generic point of $\operatorname{Spec} R$ spreads out to the nonempty open locus $D(c)$. It is used here to prove [`Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime`](thm.html#Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime), which transports primality of an ideal to its reductions at the maximal ideals of a dense open subset of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type v} [Finite σ] (F : MvPolynomial σ R)
    (hF : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (MvPolynomial.map φ F) := by sorry
