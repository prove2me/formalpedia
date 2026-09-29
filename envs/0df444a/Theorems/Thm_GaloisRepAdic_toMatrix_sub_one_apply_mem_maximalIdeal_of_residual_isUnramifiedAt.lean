-- Prove2me | Theorems.Thm_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt
-- name    : GaloisRepAdic.toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/8f78387a-1ccd-50b5-b6b4-917d17717662
-- title:
--   Residually unramified inertia acts trivially modulo 𝔪
-- statement:
--   Let $A$ be a commutative local ring with maximal ideal $\mathfrak m$ and residue field $\kappa = A/\mathfrak m$, and let $\rho$ be a [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is: a free finite $A$-module $V$ with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\sigma \mapsto \rho(\sigma)$ from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\operatorname{End}_A(V)$, and the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho(\sigma)v - v \in \mathfrak m^n \cdot V$ for all $v \in V$ and all $\sigma$ fixing $L$ pointwise. Assume the residual representation $\kappa \otimes_A V$, with $\sigma$ acting by the base change of $\rho(\sigma)$, is unramified at a natural number $q$: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$, every element of the image in $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $P$ acts on $\kappa \otimes_A V$ as the identity. Then for every $A$-basis $b$ of $V$ indexed by $\mathrm{Fin}\ 2$, every such $P$ with $q$ a nonunit of $P$, every $\sigma$ in the image of the inertia subgroup of $P$, and all $i, j \in \mathrm{Fin}\ 2$, the $(i,j)$ entry of the matrix of $\rho(\sigma)$ in the basis $b$ differs from the corresponding entry $\delta_{ij}$ of the identity matrix by an element of $\mathfrak m$; equivalently $\rho(\sigma)$ lies in the kernel of reduction $\mathrm{M}_2(A) \to \mathrm{M}_2(\kappa)$.
--
--   This records, in matrix form and in an arbitrary basis, that inertia at a prime where the residual representation is unramified acts through $1 + \mathfrak m\,\mathrm{M}_2(A)$. It is the starting point for constructing the character through which inertia at an auxiliary (Taylor–Wiles) prime acts, and is cited by [`GaloisRepAdic.exists_inertiaCharacter_of_detIsCyclotomic_of_regular`](thm.html#GaloisRepAdic.exists_inertiaCharacter_of_detIsCyclotomic_of_regular).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem GaloisRepAdic.toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ} (hunr : ρ.residual.IsUnramifiedAt q)
    (b : Module.Basis (Fin 2) A ρ.V) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (i j : Fin 2) :
    LinearMap.toMatrix b b (ρ.ρ σ) i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A := by sorry
