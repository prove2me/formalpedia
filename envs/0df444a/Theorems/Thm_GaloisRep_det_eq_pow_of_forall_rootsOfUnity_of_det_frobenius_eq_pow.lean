-- Prove2me | Theorems.Thm_GaloisRep_det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
-- name    : GaloisRep.det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/b4602e95-f19b-52c6-ab84-e02eb86df285
-- title:
--   Determinant a^m on inertia at p from Frobenius determinants ℓ^m
-- statement:
--   Let $p$ be a prime, $F$ a field of characteristic $p$, $N$ a non-zero natural number, $S$ a finite set of natural numbers, $m$ a natural number, and $\rho\colon \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q}) \to \mathrm{GL}_2(F)$ a group homomorphism, where $\overline{\mathbb Q}$ is the algebraic closure of $\mathbb Q$. Assume $\rho$ factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ with $L$ finite-dimensional over $\mathbb Q$ such that $\rho\sigma = 1$ for every $\sigma$ fixing $L$ pointwise. Assume further that for every prime $\ell$ with $\ell \nmid N$, $\ell \notin S$ and $\ell \neq p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ which is a Frobenius at $\ell$ for $A$ (that is, $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb Q$ and the induced action on the residue field of $A$ is $x \mapsto x^{\ell}$), one has $\det \rho(\sigma) = \ell^{m}$ in $F$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ having $p$ as a non-unit. Then for every $\sigma$ in the image in $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $P$ over $\mathbb Q$, and every natural number $a$ such that $\sigma\mu = \mu^{a}$ for all $\mu \in \overline{\mathbb Q}$ with $\mu^{p} = 1$, one has $\det \rho(\sigma) = a^{m}$ in $F$.
--
--   This is the inertia-at-$p$ form of the statement that the determinant of such a two-dimensional mod $p$ representation is the $m$-th power of the cyclotomic character: the determinant on an inertia element above $p$ is read off from its action on the $p$-th roots of unity. In this shape the clause is consumed by the arguments producing stable lines and absolute irreducibility for residual representations, and by the determinant computation for the Hecke torsion of the relevant modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow.lean

import Mathlib.Data.ZMod.Basic
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite) (m : ℕ)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.det (ρ σ).val = (ℓ : F) ^ m)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → Matrix.det (ρ σ).val = (a : F) ^ m := by sorry
