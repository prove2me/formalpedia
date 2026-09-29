-- Prove2me | Theorems.Thm_ModularCurve_mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense
-- name    : ModularCurve.mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/599382f3-0cd9-5188-b606-d4c33d0704e7
-- title:
--   Quadratic relation for every g on J[𝔪]
-- statement:
--   Let $\mathbb{T}=\mathbb{Z}[X_\ell:\ell\text{ prime}]$ be the polynomial algebra `HeckeAlg` with generators `heckeGen`, let $G=\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, and let $J$ be an abelian group carrying a $\mathbb{T}$-module structure and a distributive $G$-action whose scalars commute with those of $\mathbb{T}$. Fix naturals $N,p$, an ideal $\mathfrak{m}\subseteq\mathbb{T}$ with $p\in\mathfrak{m}$, and a monoid homomorphism $\rho:G\to M_2(\mathbb{T}/\mathfrak{m})$. Assume: (i) `FrobeniusQuadratic`, i.e. for every prime $\ell\nmid Np$, every valuation subring $A\subseteq\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, every $\sigma$ in the decomposition subgroup of $A$ acting on the residue field by $x\mapsto x^{\ell}$, and every $x\in J$ killed by some power of $p$, one has $\sigma^2x-X_\ell\cdot(\sigma x)+\ell x=0$; (ii) a finite set $S\subseteq\mathbb{N}$ containing every prime dividing $Np$; (iii) for each prime $\ell\notin S$ and each such $A$ and Frobenius $\sigma$ at $\ell$, the images of $X_\ell$ and of $\ell$ in $\mathbb{T}/\mathfrak{m}$ are $\operatorname{tr}\rho(\sigma)$ and $\det\rho(\sigma)$; (iv) [`FrobeniusPowerDense`](def/GaloisRep_FrobeniusPowerDense.html#L7) for $S$ and the subgroup $\ker\rho\cap\{$elements fixing $J[\mathfrak{m}]=$ `heckeTorsion J 𝔪` pointwise$\}$: every $\sigma\in G$ differs from some conjugate $g\tau^{n}g^{-1}$ of a power of a Frobenius $\tau$ at a prime $\ell\notin S$ by an element of that subgroup. Then for every $g\in G$ the $(\mathbb{T}/\mathfrak{m})$-endomorphism $x\mapsto g\cdot x$ of $J[\mathfrak{m}]$ satisfies $g^2-\operatorname{tr}\rho(g)\,g+\det\rho(g)\cdot 1=0$.
--
--   This is the Čebotarev step in Ribet's level-lowering argument: the Eichler–Shimura quadratic relation, known at Frobenius elements outside a finite set, is propagated to every element of the Galois group acting on the $\mathfrak{m}$-torsion. It supplies the annihilation hypothesis used to produce the Boston–Lenstra–Ribet direct-sum decomposition of `heckeTorsion J 𝔪` and, through that, the description of the mod-$p$ representation attached to a Weierstrass curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧ Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (heckeTorsion J 𝔪 : Set J))) :
    ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      mTorsionGaloisRep J 𝔪 g ^ 2 - (ρ g).trace • mTorsionGaloisRep J 𝔪 g + (ρ g).det • 1 = 0 := by sorry
