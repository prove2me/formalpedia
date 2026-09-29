-- Prove2me | Theorems.Thm_GaloisRep_forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow
-- name    : GaloisRep.forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/124e4e77-4a6b-5130-a354-2bd149104b37
-- title:
--   Level-two inertia eigenvector forces no stable line
-- statement:
--   Let $p$ be a prime, $F$ a field, and $\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to \mathrm{GL}_2(F)$ a group homomorphism (with $\overline{\mathbb Q}$ the chosen algebraic closure of $\mathbb Q$ and the Galois group realised as its $\mathbb Q$-algebra automorphisms) which factors through a finite level: there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that $\rho\sigma=1$ whenever $\sigma$ fixes $L$ pointwise. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $P$, and let $\pi\in\overline{\mathbb Q}$ satisfy $\pi^{p^2-1}=p$; write $\omega$ for the associated tame character, sending $\sigma$ to the residue of $\sigma\pi/\pi$ in the residue field of $P$ when $\sigma\pi/\pi\in P$ and to $0$ otherwise, and let $I$ be the image in the full Galois group of the inertia subgroup of $P$ over $\mathbb Q$ (pushed forward along the inclusion of the decomposition subgroup). Let $\psi\colon F\to \mathrm{ResidueField}(P)$ be a ring homomorphism and $k$ a natural number with $2\le k\le p+1$. Assume there is a nonzero vector $v$ in $\mathrm{ResidueField}(P)^2$ such that, for all $\sigma\in I$, the matrix $\psi(\rho\sigma)$ satisfies either $\psi(\rho\sigma)v=\omega(\sigma)^{k-1}v$ for all such $\sigma$, or $\psi(\rho\sigma)v=(\omega(\sigma)^{p})^{k-1}v$ for all such $\sigma$. Then for every nonzero $u\in (\overline F)^2$, where $\overline F$ is the algebraic closure of $F$, there exists $\sigma$ in the Galois group with $\rho(\sigma)u$, computed from the entrywise image of $\rho\sigma$ in $\overline F$, outside the $\overline F$-line spanned by $u$.
--
--   This is the absolute irreducibility of a two-dimensional mod-$p$ Galois representation in the shape 'no Galois-stable line over $\overline F$', deduced from the occurrence of a fundamental character of level two (or its $p$-th power) on inertia at $p$ in the Serre weight range $2\le k\le p+1$. It is applied in the analysis of residual representations attached to weight-two eigenforms killed by a Hecke operator, via [`GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_theta_heckeT_eq_zero_of_det_eq_pow_of_eq_two`](thm.html#GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_theta_heckeT_eq_zero_of_det_eq_pow_of_eq_two), the point being that characters of level two do not extend to characters of the decomposition group, whose inertia values are $(p-1)$-st roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    (ψk : F →+* IsLocalRing.ResidueField P) (kn : ℕ) (hk2 : 2 ≤ kn) (hkp : kn ≤ p + 1)
    (hv : ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map ψk).mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map ψk).mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v)))
    (u : Fin 2 → AlgebraicClosure F) (hu : u ≠ 0) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Matrix.mulVec ((ρ σ).val.map (algebraMap F (AlgebraicClosure F))) u ∉
        (AlgebraicClosure F) ∙ u := by sorry
