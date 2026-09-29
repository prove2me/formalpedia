-- Prove2me | Theorems.Thm_ModularCurve_det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast
-- name    : ModularCurve.det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/cdbe79db-901b-5cc1-8260-16948bc252e8
-- title:
--   Determinant equals the exponent of σ on p-th roots of unity
-- statement:
--   Fix a prime $p$ and a maximal ideal $\mathfrak m$ of `HeckeAlg` $= \mathrm{MvPolynomial}\ \mathbb{Z}$ in the primes, with the image of $p$ lying in $\mathfrak m$, so that the residue ring $\mathrm{HeckeAlg}/\mathfrak m$ is a field of characteristic $p$. Let $\rho$ be a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$ to $2\times 2$ matrices over $\mathrm{HeckeAlg}/\mathfrak m$ which factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that $\rho\sigma = 1$ whenever $\sigma$ fixes $L$ pointwise. Let $S$ be a finite set of naturals, and assume that for every prime $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb Q$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\det\rho(\sigma) = \ell$ in $\mathrm{HeckeAlg}/\mathfrak m$. The conclusion is that for every $\sigma$ and every natural number $a$ such that $\sigma\mu = \mu^{a}$ for all $\mu \in \overline{\mathbb Q}$ with $\mu^{p} = 1$, one has $\det\rho(\sigma) = a$ in $\mathrm{HeckeAlg}/\mathfrak m$. Note that the Frobenius hypothesis here is imposed at all primes outside $S$, with no exclusion of $\ell = p$.
--
--   This identifies the determinant of a residual two-dimensional representation over a residue field of the Hecke algebra with the mod-$p$ cyclotomic character, expressed through the exponent by which a Galois element acts on $p$-th roots of unity; in this shape the determinant can be evaluated on inertia at $p$ without reference to any Frobenius element. It is used in the analysis of the toric monodromy part, in [`ModularCurve.finrank_span_toricMonodromyPart_le_of_not_dvd_sub_one_of_attachedBlr`](thm.html#ModularCurve.finrank_span_toricMonodromyPart_le_of_not_dvd_sub_one_of_attachedBlr).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.det_eq_natCast_of_forall_rootsOfUnity_of_det_frobenius_eq_natCast
    (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (S : Finset ℕ)
    (hdet : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → (ρ σ).det = (a : HeckeAlg ⧸ 𝔪) := by sorry
