-- Prove2me | Theorems.Thm_ModularCurve_not_isEventuallyEisenstein_of_repClauses
-- name    : ModularCurve.not_isEventuallyEisenstein_of_repClauses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/8932c25b-7801-53c1-b6bd-eb8dd75c6c1b
-- title:
--   Irreducibility excludes eventually Eisenstein maximal ideals
-- statement:
--   Let $\mathbb{T}=\mathrm{MvPolynomial}\,\mathrm{Nat.Primes}\,\mathbb{Z}$ be the polynomial ring on one generator $\mathrm{heckeGen}\,\ell=X_\ell$ per prime, let $\mathfrak m\subset\mathbb{T}$ be a maximal ideal, and write $k=\mathbb{T}/\mathfrak m$ (a field, by maximality). Let $\rho$ be a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, to $2\times 2$ matrices over $k$, subject to: (i) every $k$-submodule $W\subseteq k^2$ with $(\rho g)\cdot v\in W$ for all $g$ and all $v\in W$ is $\bot$ or $\top$; (ii) for a finite set $S_\rho\subset\mathbb{N}$, every prime $\ell\notin S_\rho$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acting on the residue field of $A$ as $x\mapsto x^{\ell}$, one has $\operatorname{tr}\rho(\sigma)=X_\ell \bmod \mathfrak m$ and $\det\rho(\sigma)=\ell \bmod \mathfrak m$; (iii) there is a number field $F$, Galois over $\mathbb{Q}$ and embedded in $\overline{\mathbb{Q}}$ compatibly with $\mathbb{Q}$, such that the kernel of restriction $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to\mathrm{Gal}(F/\mathbb{Q})$ lies in $\ker\rho$. Then $\mathfrak m$ is not eventually Eisenstein: there is no finite set $S$ of primes with $X_\ell-(\ell+1)\in\mathfrak m$ for every prime $\ell\notin S$.
--
--   This is the non-Eisenstein step in the Mazur-principle/level-lowering circle of ideas: an irreducible two-dimensional mod-$\mathfrak m$ representation whose Frobenius traces and determinants are given by the Hecke generators and the cyclotomic character cannot have Eisenstein congruences at almost all primes. It is stated at the level of an abstract maximal ideal of the free Hecke algebra, with an arbitrary finite exceptional set, and is used in the residual modularity step [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_not_isEventuallyEisenstein_of_repClauses.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.not_isEventuallyEisenstein_of_repClauses
    (𝔪 : Ideal ModularCurve.HeckeAlg) (hmax : 𝔪.IsMaximal)
    (ρmat : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ModularCurve.HeckeAlg ⧸ 𝔪))
    (hirr : ∀ Wsub : Submodule (ModularCurve.HeckeAlg ⧸ 𝔪) (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪),
      (∀ g, ∀ v ∈ Wsub, (ρmat g).mulVec v ∈ Wsub) → Wsub = ⊥ ∨ Wsub = ⊤)
    (Sρ : Finset ℕ)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ Sρ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).trace = Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩))
    (hdet : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ Sρ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).det = ((ℓ : ℕ) : ModularCurve.HeckeAlg ⧸ 𝔪))
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρmat.ker) :
    ¬ ModularCurve.IsEventuallyEisenstein 𝔪 := by sorry
