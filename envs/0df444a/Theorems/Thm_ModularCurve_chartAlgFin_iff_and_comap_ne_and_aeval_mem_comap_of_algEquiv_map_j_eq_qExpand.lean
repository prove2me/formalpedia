-- Prove2me | Theorems.Thm_ModularCurve_chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand
-- name    : ModularCurve.chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/b718209e-8ed5-562a-a205-6f8530a859cc
-- title:
--   Automorphisms with σ(j)=j(qᵖ) fix the j-chart, move the Gauss ring
-- statement:
--   Let $p$ be a prime, $L$ a field of characteristic zero, and $K$ an intermediate field of the Laurent series field $L((q))$ over $L$. Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$, and let $K$ carry an $A$-algebra structure compatible with that of $L$. Let $j \in K$ be a nonzero element whose image in $L((q))$ is the coefficientwise image under $\mathbb{Q} \to L$ of $\mathrm{jq} = q^{-1}\cdot(\text{the rational power series } \mathrm{jNumQ})$, and let $\sigma$ be an $L$-algebra automorphism of $K$ such that the image of $\sigma(j)$ in $L((q))$ is the coefficientwise image of the substitution $q \mapsto q^p$ (multiplication by $p$ on the exponent group $\mathbb{Z}$) applied to $\mathrm{jq}$. Then two things hold. First, for every $b \in K$, $b$ is integral over the $A$-subalgebra $A[j] = \mathrm{Algebra.adjoin}\,A\,\{j\}$ of $K$ if and only if $\sigma(b)$ is; that is, the subalgebra $\mathrm{chartAlgFin}\,A\,K\,j$ of elements of $K$ integral over $A[j]$ is $\sigma$-stable in both directions. Second, let $W_0$ be any valuation subring of $K$ whose membership is given by Gauss presentations over $A$: $f \in W_0$ if and only if there are $x, y \in A[[q]]$ with the reduction of $y$ modulo the maximal ideal of $A$ nonzero and $f \cdot y = x$ in $L((q))$, the power series being mapped to $L$ coefficientwise. Then the preimage $\sigma^{-1}(W_0)$, formed as the comap of $W_0$ along the ring homomorphism underlying $\sigma$, is different from $W_0$, and for every polynomial $P \in A[X]$ whose reduction modulo the maximal ideal of $A$ is nonzero, both $P(j)$ and $P(j)^{-1}$ lie in $\sigma^{-1}(W_0)$.
--
--   This is the level-free form of the $p$-twist statements for fields of $q$-expansions: the only input about $\sigma$ is that it sends the $q$-expansion of $j$ to that of $j(q^p)$, and the conclusions are the $\sigma$-stability of the integral $j$-finite chart together with the assertion that $\sigma$ moves a Gauss valuation ring while keeping all $P(j)^{\pm 1}$ inside its translate. It is the common engine behind the twist statements for the function fields of $X_1(Mp)$ and of $X(\Gamma_1(M) \cap \Gamma_0(p))$, and is used in the analysis of the two branches of the reduction of the modular curve and of the residue fields at the Gauss valuations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσ : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) :
    (∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
      σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ∧
    (∀ W₀ : ValuationSubring ↥K,
      (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
      W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
        (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom)) := by sorry
