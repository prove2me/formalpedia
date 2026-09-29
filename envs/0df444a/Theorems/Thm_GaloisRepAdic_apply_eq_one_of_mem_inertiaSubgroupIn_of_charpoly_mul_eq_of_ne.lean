-- Prove2me | Theorems.Thm_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne
-- name    : GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/90fc65c5-4b5e-57c6-8d71-c51992b0f0c9
-- title:
--   Unramifiedness at q from inertia-invariant characteristic polynomials
-- statement:
--   Let $O$ be a Noetherian local integral domain of characteristic zero, and let $\rho$ be an adic Galois representation over $O$ in the project's sense: a free finite $O$-module $V$ with $\operatorname{rank}_O V = 2$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ (with $\overline{\mathbb Q}$ the algebraic closure of $\mathbb Q$) to $\operatorname{End}_O(V)$, together with the continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that $\rho(\sigma)v - v \in \mathfrak m^n \cdot V$ for all $v \in V$ and all $\sigma$ fixing $L$ pointwise, $\mathfrak m$ the maximal ideal of $O$. Let $p$ be a prime with $p \in \mathfrak m$, let $q$ be a prime with $p \neq q$, and let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$. Write $I_P$ for the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup. Assume that the characteristic polynomial of $\rho$ is invariant under left translation by $I_P$: $\operatorname{charpoly}(\rho(\sigma g)) = \operatorname{charpoly}(\rho(g))$ for all $\sigma \in I_P$ and all $g$. Assume further that $\tau$ lies in the decomposition subgroup of $P$ and acts on the residue field of $P$ by $x \mapsto x^q$, and that $q \cdot \operatorname{tr}(\rho(\tau))^2 \neq (q+1)^2 \det(\rho(\tau))$ in $O$. Then $\rho(\sigma) = 1$ for every $\sigma \in I_P$.
--
--   This transfers unramifiedness at $q$ along an equality of characteristic polynomials, with no irreducibility assumed: a rank-two representation whose characteristic polynomials are unchanged by left multiplication by inertia at $q$ is unramified at $q$, unless the Frobenius eigenvalues at $q$ are in the degenerate ratio excluded by the last hypothesis. It is used in the analysis of eigenforms occurring at a divided level, via [`CuspForm.IsEigenformWith.inertia_eq_one_and_isRoot_charpoly_of_eigenpacketOccursAt_div`](thm.html#CuspForm.IsEigenformWith.inertia_eq_one_and_isRoot_charpoly_of_eigenpacketOccursAt_div); the proof cites [`ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_frobConj`](thm.html#ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_frobConj), which produces $p$-power roots of the commutator expression $\tau\sigma\tau^{-1}(\sigma^{q})^{-1}$ inside inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne.lean

import Definitions.Def_GaloisRep_Adic
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing Polynomial

theorem GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_charpoly_mul_eq_of_ne
    {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]
    (ρ : GaloisRepAdic O) {p : ℕ} (hp : p.Prime) (hpO : (p : O) ∈ maximalIdeal O)
    {q : ℕ} (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hcp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ.ρ (σ * g)) = LinearMap.charpoly (ρ.ρ g))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : P.IsFrobeniusAt τ q)
    (hne : (q : O) * LinearMap.trace O ρ.V (ρ.ρ τ) ^ 2 ≠ ((q : O) + 1) ^ 2 * LinearMap.det (ρ.ρ τ)) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1 := by sorry
