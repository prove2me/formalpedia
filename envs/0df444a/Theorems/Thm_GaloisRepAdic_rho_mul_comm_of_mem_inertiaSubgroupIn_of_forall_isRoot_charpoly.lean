-- Prove2me | Theorems.Thm_GaloisRepAdic_rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly
-- name    : GaloisRepAdic.rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/dd565093-1c1f-5a37-9031-4fab62dfa081
-- title:
--   Inertia acts commutatively when 1 is an eigenvalue
-- statement:
--   Let $A$ be a Noetherian local integral domain and let $\rho$ be an adic Galois representation over $A$ in the sense of the structure [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16): a free $A$-module $V$ of finite type with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho.\rho$ from $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ (with $\overline{\mathbb{Q}}$ the algebraic closure `AlgebraicClosure ℚ`) to $\operatorname{End}_A(V)$, subject to adic continuity: for every $n$ there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, such that every automorphism fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_A^n\,V$ for all $v \in V$. Let $q$ be a prime number whose image in $A$ is a unit, and let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $P$. Write $I_P$ for the inertia subgroup of $P$ over $\mathbb{Q}$, viewed as a subgroup of the full Galois group via the inclusion of the decomposition subgroup. Assume that for every $\sigma \in I_P$ the characteristic polynomial of the $A$-linear endomorphism $\rho(\sigma)$ vanishes at $1$. Then for all $\sigma, \tau \in I_P$ one has $\rho(\sigma)\rho(\tau) = \rho(\tau)\rho(\sigma)$ in $\operatorname{End}_A(V)$.
--
--   The statement says that, under the hypothesis that $1$ is an eigenvalue of every inertia element at a place above $q$ (with $q$ invertible in the coefficient ring), the image of inertia under a rank-two adic representation is abelian. It feeds the lattice and eigenline computation in the ramified principal series analysis of the Galois representation attached to a primitive form, namely [`CuspForm.IsPrimitiveForm.exists_galoisRepAdic_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor`](thm.html#CuspForm.IsPrimitiveForm.exists_galoisRepAdic_linearIndependent_inertia_apply_eq_smul_of_dvd_of_not_sq_dvd_of_dvd_conductor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.rho_mul_comm_of_mem_inertiaSubgroupIn_of_forall_isRoot_charpoly
    {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (ρ : GaloisRepAdic A) {q : ℕ} (hq : q.Prime) (hqA : IsUnit (q : A))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (h1 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (LinearMap.charpoly (ρ.ρ σ)).IsRoot 1)
    {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ = ρ.ρ τ * ρ.ρ σ := by sorry
