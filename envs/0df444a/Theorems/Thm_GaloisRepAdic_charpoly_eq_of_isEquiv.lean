-- Prove2me | Theorems.Thm_GaloisRepAdic_charpoly_eq_of_isEquiv
-- name    : GaloisRepAdic.charpoly_eq_of_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/452301e0-a84d-5bb2-98a2-a82c9f574a71
-- title:
--   Equivalent adic Galois representations have equal characteristic polynomials
-- statement:
--   Let $A$ be a commutative local ring, and let $\rho_1,\rho_2$ be two objects of type [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): each consists of a free $A$-module $V$ of finite type with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\operatorname{End}_A V$, and the continuity condition [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9), namely that for every $n$ there is a finite-dimensional intermediate field $L/\mathbb{Q}$ inside the algebraic closure such that every automorphism fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_A^n \cdot V$ for all $v \in V$. Assume `ρ₁.IsEquiv ρ₂`, i.e. there exists an $A$-linear isomorphism $e : \rho_1.V \to \rho_2.V$ with $e(\rho_1(\sigma)x) = \rho_2(\sigma)(e x)$ for all $\sigma$ and all $x$. Then for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, the characteristic polynomials of the endomorphisms $\rho_1(\sigma)$ and $\rho_2(\sigma)$ of the respective modules agree as elements of $A[X]$.
--
--   This is the standard invariance of characteristic polynomials — hence of traces and determinants — under isomorphism of representations, which is what allows statements about traces of Frobenius elements to be read off an equivalence class rather than a particular model. It is used throughout the deformation-theoretic and Hecke-theoretic parts of the argument, where lifts are only specified up to equivalence, for instance in the uniqueness clauses attached to the Hecke Galois representation data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_charpoly_eq_of_isEquiv.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.charpoly_eq_of_isEquiv {A : Type} [CommRing A] [IsLocalRing A] {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) := by sorry
