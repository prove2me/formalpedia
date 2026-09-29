-- Prove2me | Theorems.Thm_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow
-- name    : GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/cd97c578-a8f8-5e44-b628-edc7c9b78848
-- title:
--   Frobenius twist of coefficients preserves the level-two inertia alternative
-- statement:
--   Let $p$ be a prime and let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$ (the predicate `LiesOverPrime`), with residue field $k_P$. Let $\pi \in \overline{\mathbb Q}$ satisfy $\pi^{p^2-1} = p$, and let $\omega =$ `P.tameCharacter π` be the function sending $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to the residue of $\sigma\pi/\pi$ in $k_P$ when $\sigma\pi/\pi \in P$, and to $0$ otherwise. Let $\rho$ be a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{GL}_2(k_P)$, let $\varphi\colon k_P \to k_P$ be a ring homomorphism with $\varphi(x) = x^{p^j}$ for all $x$, for some $j \in \mathbb N$, and let $k_n \in \mathbb N$. Write $I$ for the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ inside its decomposition subgroup. Assume there is a nonzero $v \in k_P^2$ such that either $\rho(\sigma)v = \omega(\sigma)^{k_n-1}v$ for all $\sigma \in I$, or $\rho(\sigma)v = (\omega(\sigma)^p)^{k_n-1}v$ for all $\sigma \in I$ (with $k_n - 1$ truncated subtraction in $\mathbb N$). Then the same alternative holds for the representation obtained by applying $\varphi$ to the matrix entries of $\rho$: there is a nonzero $w \in k_P^2$ with $\varphi(\rho(\sigma))w = \omega(\sigma)^{k_n-1}w$ for all $\sigma \in I$, or $\varphi(\rho(\sigma))w = (\omega(\sigma)^p)^{k_n-1}w$ for all $\sigma \in I$.
--
--   This records the stability, under a Frobenius twist of the coefficient field, of the shape of inertia predicted for a supersingular-type residual representation: the unordered pair of tame characters $\{\omega^{k_n-1}, (\omega^p)^{k_n-1}\}$ of level two is preserved, only the two disjuncts possibly being interchanged. It is used in [`GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_theta_heckeT_eq_zero_of_det_eq_pow_of_eq_two`](thm.html#GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_theta_heckeT_eq_zero_of_det_eq_pow_of_eq_two), where two reductions of a Hecke eigensystem differing by a power of Frobenius have to be matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow
    (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      GL (Fin 2) (IsLocalRing.ResidueField P))
    (φ : IsLocalRing.ResidueField P →+* IsLocalRing.ResidueField P) (j : ℕ)
    (hφ : ∀ x, φ x = x ^ p ^ j) (kn : ℕ)
    (h : ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ σ).val.mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ σ).val.mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v))) :
    ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map φ).mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map φ).mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v)) := by sorry
