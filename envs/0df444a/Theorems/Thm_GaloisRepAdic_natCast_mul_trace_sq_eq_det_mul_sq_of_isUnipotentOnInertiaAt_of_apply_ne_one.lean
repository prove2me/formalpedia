-- Prove2me | Theorems.Thm_GaloisRepAdic_natCast_mul_trace_sq_eq_det_mul_sq_of_isUnipotentOnInertiaAt_of_apply_ne_one
-- name    : GaloisRepAdic.natCast_mul_trace_sq_eq_det_mul_sq_of_isUnipotentOnInertiaAt_of_apply_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/0ebf792b-c1b1-54c2-8c59-4183d3c6864d
-- title:
--   Steinberg trace identity at a ramified unipotent prime
-- statement:
--   Let $A$ be a commutative Noetherian local domain and let $\rho$ be a two-dimensional $\mathfrak m$-adic Galois representation over $A$ in the sense of [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16): a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$, together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$ to $\mathrm{End}_A(V)$ which is $\mathfrak m$-adically continuous, meaning that for every $n$ there is a finite subextension $L/\mathbb Q$ of $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in (\mathfrak m^n)\cdot V$ for all $v \in V$. Let $p$ be a prime whose image in $A$ lies in the maximal ideal, and let $q$ be a prime with $q \neq p$. Assume $\rho$ is unipotent on inertia at $q$: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$, and every element of the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$, the characteristic polynomial of its image under $\rho$ is $(X-1)^2$. Let $P$ be such a valuation subring ($q$ a non-unit of $P$) at which $\rho$ is genuinely ramified, that is, some $\tau$ in the image of the inertia subgroup has $\rho(\tau) \neq 1$, and let $\sigma$ be a Frobenius element at $P$ for $q$: $\sigma$ lies in the decomposition subgroup of $P$ over $\mathbb Q$ and acts on the residue field of $P$ by $x \mapsto x^q$. Then in $A$ one has $q \cdot \operatorname{tr}(\rho(\sigma))^2 = \det(\rho(\sigma)) \cdot (q+1)^2$, the trace and determinant being those of the $A$-endomorphism $\rho(\sigma)$ of $V$.
--
--   This is the trace–determinant signature of the special (Steinberg) local shape at $q$, where $\rho$ restricted to the decomposition group at $q$ is an unramified twist of $\begin{pmatrix}\varepsilon & *\\ 0 & 1\end{pmatrix}$: the identity records $\operatorname{tr} = \mu(\sigma)(q+1)$, $\det = \mu(\sigma)^2 q$ without naming the unramified character $\mu$ or choosing a basis. It is used in the criterion [`CuspForm.TWLevel.HeckeRing.isUnramifiedAt_of_not_dvd_sub_one_of_trace_frobenius_sq_ne`](thm.html#CuspForm.TWLevel.HeckeRing.isUnramifiedAt_of_not_dvd_sub_one_of_trace_frobenius_sq_ne), which deduces unramifiedness at $q$ from the failure of this equality; the proof here uses the tame relation $\sigma\tau\sigma^{-1}\tau^{-q} \in I_P^{p^n}$ supplied by [`ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_frobConj`](thm.html#ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_frobConj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_natCast_mul_trace_sq_eq_det_mul_sq_of_isUnipotentOnInertiaAt_of_apply_ne_one.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.natCast_mul_trace_sq_eq_det_mul_sq_of_isUnipotentOnInertiaAt_of_apply_ne_one
    {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p)
    (hunip : ρ.IsUnipotentOnInertiaAt q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ τ ≠ 1)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ q) :
    (q : A) * ρ.trace σ ^ 2 = LinearMap.det (ρ.ρ σ) * ((q : A) + 1) ^ 2 := by sorry
