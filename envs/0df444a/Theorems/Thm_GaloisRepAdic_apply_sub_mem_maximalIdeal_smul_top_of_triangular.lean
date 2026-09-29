-- Prove2me | Theorems.Thm_GaloisRepAdic_apply_sub_mem_maximalIdeal_smul_top_of_triangular
-- name    : GaloisRepAdic.apply_sub_mem_maximalIdeal_smul_top_of_triangular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/7e51a212-9412-5ad6-9fcf-14a63699d962
-- title:
--   Unipotent-modulo-𝔪 triangular action is trivial on V/𝔪 V
-- statement:
--   Let $B$ be a commutative local ring and let $\rho$ be a [`GaloisRepAdic B`](def/GaloisRep_Adic.html#L16), that is: a $B$-module $V$ which is free and finite of rank $2$ over $B$, together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ (the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to the $B$-linear endomorphisms of $V$, satisfying the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v-v\in\mathfrak m^n\cdot V$ for all $v$. Fix such a $\sigma$, a $B$-basis $b=(b_0,b_1)$ of $V$ indexed by `Fin 2`, and elements $x,y,z\in B$ with $\rho(\sigma)b_0=x\,b_0$ and $\rho(\sigma)b_1=y\,b_0+z\,b_1$, so that $\rho(\sigma)$ is upper triangular with diagonal $(x,z)$ in this basis. Assume $x-1$, $y$ and $z-1$ all lie in the maximal ideal $\mathfrak m$ of $B$. Then for every $v\in V$ one has $\rho(\sigma)v-v\in\mathfrak m\cdot V$, where $\mathfrak m\cdot V$ denotes the submodule $\mathfrak m\cdot\top$.
--
--   This is the elementary bookkeeping step saying that a triangular matrix congruent to the identity modulo the maximal ideal acts trivially on the residual module $V/\mathfrak m V$. It is used in the derivation of the residual (peu-ramifié type) conclusion, being cited by [`GaloisRepAdic.exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle`](thm.html#GaloisRepAdic.exists_root_one_add_prime_inertia_sub_mem_of_quotientScalar_sq_sub_one_mem_span_socle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_apply_sub_mem_maximalIdeal_smul_top_of_triangular.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.apply_sub_mem_maximalIdeal_smul_top_of_triangular
    {B : Type} [CommRing B] [IsLocalRing B] (ρ : GaloisRepAdic B)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Module.Basis (Fin 2) B ρ.V) (x y z : B)
    (h0 : ρ.ρ σ (b 0) = x • b 0) (h1 : ρ.ρ σ (b 1) = y • b 0 + z • b 1)
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal B) (hy : y ∈ IsLocalRing.maximalIdeal B)
    (hz : z - 1 ∈ IsLocalRing.maximalIdeal B) (v : ρ.V) :
    ρ.ρ σ v - v ∈ (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B ρ.V) := by sorry
