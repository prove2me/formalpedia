-- Prove2me | Theorems.Thm_ModularCurve_exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot
-- name    : ModularCurve.exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/dcf4f5c8-d6e4-5310-aa37-3dc7761a958a
-- title:
--   Residual two-dimensional representation at a Hecke maximal ideal
-- statement:
--   Let $M$ be a non-zero natural number and let $\mathfrak m$ be a maximal ideal of the Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb Z[X_\ell : \ell \text{ prime}]$ with $X_\ell =$ `heckeGen` $\ell$. Give the Jacobian $J_0(M) =$ `JZero M`, the degree-zero divisor class group of the base-changed modular function field of level $M$ over $\overline{\mathbb Q}$, its `HeckeAlg`-module structure `heckeModuleBar M`, and assume that its $\mathfrak m$-torsion, the submodule of elements annihilated by every element of $\mathfrak m$, is non-zero. Then there is a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (as the group of $\mathbb Q$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb Q$) to the multiplicative monoid of $2\times 2$ matrices over the residue field `HeckeAlg ⧸ 𝔪` with the following three properties. First, $\rho$ factors through a finite level: there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that $\rho\sigma = 1$ for every $\sigma$ fixing $L$ pointwise. Second, there is a finite set $S$ of natural numbers such that for every prime $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, the image of $X_\ell$ in `HeckeAlg ⧸ 𝔪` is the trace of $\rho\sigma$ and the image of $\ell$ is its determinant. Third, either the `HeckeAlg ⧸ 𝔪`-span of the range of $\rho$ is the whole matrix algebra, or the image of $\rho$ is commutative. Invertibility of the matrices $\rho\sigma$ is not asserted.
--
--   This is the construction, in the style of Eichler–Shimura and of Ribet's work on representations arising from modular forms, of the two-dimensional residual Galois representation attached to a maximal ideal $\mathfrak m$ of the Hecke algebra whose torsion in $J_0(M)$ is non-zero, with the Eichler–Shimura relations $\operatorname{tr}\rho(\mathrm{Frob}_\ell) = T_\ell$, $\det\rho(\mathrm{Frob}_\ell) = \ell$ away from a finite set of primes, together with the dichotomy absolutely irreducible / commutative image. It is used to analyse the $\mathfrak m$-torsion of $J_0(M)$ as a Galois module, in particular to show that in the absolutely irreducible case it becomes two-dimensional after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot
    (M : ℕ) [NeZero M] (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    (hsupp : letI := heckeModuleBar M; heckeTorsion (JZero M) 𝔪 ≠ ⊥) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∃ S : Finset ℕ, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
          Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
            Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det) ∧
      (Submodule.span (HeckeAlg ⧸ 𝔪)
          (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g)) = ⊤ ∨
        ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ * ρ τ = ρ τ * ρ σ) := by sorry
