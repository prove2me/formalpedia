-- Prove2me | Theorems.Thm_GaloisRepAdic_charpoly_residual
-- name    : GaloisRepAdic.charpoly_residual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/301c68f2-b611-5ab7-b9ae-2bad4704c7b4
-- title:
--   Characteristic polynomial of the residual representation
-- statement:
--   Let $A$ be a commutative local ring with residue field $\kappa = A/\mathfrak m$ and residue map `IsLocalRing.residue A`, and let $\rho$ be a [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a free, finite $A$-module $V$ with $\operatorname{rank}_A V = 2$ together with a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $\operatorname{End}_A V$ which is adically continuous in the sense that for every $n$ there is a finite-dimensional intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in (\mathfrak m^n)\cdot V$ for all $v \in V$. Let $\sigma$ be such an automorphism. The assertion is that the characteristic polynomial of the endomorphism $\rho.\mathrm{residual}.\rho(\sigma)$ of the $\kappa$-vector space $\kappa \otimes_A V$ — that is, of the base change of $\rho(\sigma)$ along $A \to \kappa$, which is how `residual` is defined — is the image of the characteristic polynomial of $\rho(\sigma) \in \operatorname{End}_A V$ under the coefficientwise map induced by $A \to \kappa$.
--
--   This is the compatibility of characteristic polynomials (hence of traces and determinants) with reduction modulo the maximal ideal, for the residual representation attached to an adic two-dimensional representation. It is used whenever a congruence between traces of Frobenius modulo $\mathfrak m$ is to be transported into the vocabulary of residual representations, for instance in identifying the residual representation of a Hecke-theoretic representation with the one attached to an eigenform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_charpoly_residual.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem GaloisRepAdic.charpoly_residual {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ.residual.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map (IsLocalRing.residue A) := by sorry
