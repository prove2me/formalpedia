-- Prove2me | Theorems.Thm_ModularCurve_exists_character_frobeniusQuadratic_diamondTwist_tateModule_jH
-- name    : ModularCurve.exists_character_frobeniusQuadratic_diamondTwist_tateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/e5e9e03c-1e09-501c-bdd2-d9f16ca779b3
-- title:
--   Eichler–Shimura relation on TₚJ_H(M) after diamond twisting
-- statement:
--   Let $M\ge 1$ be a natural number, $p$ a prime, $H$ a subgroup of $(\mathbb{Z}/M)^\times$ and $S$ an arbitrary set of natural numbers. Write $G=\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ for the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, $J=$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) for the group of degree-zero divisor classes (degree-zero divisors modulo principal divisors) of the function field `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, and $T_pJ=$ [`TateModule p J`](def/EllipticCurve_TateModule.html#L15) for the group of sequences $(x_n)_{n\in\mathbb{N}}$ in $J$ with $p^nx_n=0$ and $px_{n+1}=x_n$, a $\mathbb{Z}_p$-module. The assertion is that there is a multiplicative homomorphism $\delta\colon G\to(\mathbb{Z}/M)^\times$ with the following three properties. First, $\delta$ is unramified outside $M$: for every prime $q\nmid M$, every valuation subring $A\subseteq\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, and every $\sigma$ in the image in $G$ of the inertia subgroup of $A$ over $\mathbb{Q}$, one has $\delta(\sigma)=1$. Secondly, $\delta$ factors through a finite level: there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $\delta(\sigma)=1$ whenever $\sigma$ fixes $L$ pointwise. Thirdly, there is a homomorphism $\rho'\colon G\to\mathrm{End}_{\mathbb{Z}_p}(T_pJ)$ such that, for every $\sigma\in G$, $\rho'(\sigma)$ is the composite of the coefficientwise action of $\sigma$ on $T_pJ$ followed by the diamond operator $\langle\delta(\sigma)\rangle$ induced on $T_pJ$ by `diamondHBar M H (δ σ)`, and such that the quadratic relation $$\rho'(\sigma)^2x-T_\ell\bigl(\rho'(\sigma)x\bigr)+\ell\cdot\langle\ell\bmod M\rangle x=0$$ holds for all $x\in T_pJ$, for every prime $\ell\notin S$ with $\ell\nmid M$ and $\ell\ne p$, every valuation subring $A\subseteq\overline{\mathbb{Q}}$ having $\ell$ as a non-unit, and every $\sigma$ that is a Frobenius at $\ell$ for $A$, i.e. $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x\mapsto x^\ell$. Here $T_\ell$ and $\langle\,\cdot\,\rangle$ denote the endomorphisms of $T_pJ$ induced by `heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ` and by `diamondHBar M H`, and $\ell\bmod M$ is the unit given by $\ell$ being coprime to $M$.
--
--   This is the Eichler–Shimura congruence relation for the Jacobian of $X_H(M)$ in the normalisation with trace $T_\ell$ and determinant $\ell\langle\ell\rangle$, obtained from the untwisted relation $\langle\ell\rangle\sigma^2-T_\ell\sigma+\ell=0$ by twisting the Galois action by a diamond character unramified outside $M$ and of finite level. It is used in the construction of a finite-level faithful Galois–Hecke lattice inside the Tate module of $J_H(M)$, and hence in the attachment of Galois representations to Hecke eigenforms of level coprime to the residual characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_character_frobeniusQuadratic_diamondTwist_tateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_character_frobeniusQuadratic_diamondTwist_tateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) :
    ∃ (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod M)ˣ),

      (∀ (q : ℕ), q.Prime → ¬ q ∣ M → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, δ σ = 1) ∧

      GaloisFactorsThroughFiniteLevel δ ∧

      ∃ ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
          Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH M H)),
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          ρ' σ = ModularCurve.tateGenOpH M H S p (CohCarrier.Gen.dia (δ σ)) *
            ModularCurve.JH.tateGaloisRep M H p σ) ∧

        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
          ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
            ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
              ∀ x : ↥(TateModule p (ModularCurve.JH M H)),
                ρ' σ (ρ' σ x) - ModularCurve.tateGenOpH M H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) (ρ' σ x)
                  + ℓ • ModularCurve.tateGenOpH M H S p
                      (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ
                        ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))) x = 0 := by sorry
