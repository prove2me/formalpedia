-- Prove2me | Theorems.Thm_ModularCurve_forall_algebraMap_mem_comap_and_forall_aeval_mem_comap_gauss_of_coe_map_eq_qExpand
-- name    : ModularCurve.forall_algebraMap_mem_comap_and_forall_aeval_mem_comap_gauss_of_coe_map_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/28981a3f-5b0b-526e-b8fe-505694d7d871
-- title:
--   Frobenius-twisted Gauss ring is a branch ring over j
-- statement:
--   Let $p$ be a prime, $L$ a field of characteristic zero, and $K$ an intermediate field of the Laurent series field $L((q))$ over $L$. Let $A$ be a discrete valuation domain with fraction field $L$, made an $A$-algebra tower $A \to L \to K$, and assume $p \in \mathfrak m_A$. Let $j \in K$ have image in $L((q))$ equal to $\mathrm{coeffEmb}\,L\,\mathrm{jq}$, the coefficientwise image along $\mathbb Q \to L$ of $q^{-1}$ times the power series $\mathrm{jNumQ}$. Let $W_0$ be a valuation subring of $K$ characterised by: $f \in W_0$ iff there are $x, y \in A[[q]]$ with $y \bmod \mathfrak m_A \neq 0$ and $f \cdot y = x$ in $L((q))$ after mapping coefficients $A \to L$. Let $\sigma$ be an $L$-algebra automorphism of $K$ whose value $\sigma j$ has image $\mathrm{coeffEmb}\,L(\mathrm{qExpand}\,\mathbb Q\,p\,\mathrm{jq})$, the substitution $q \mapsto q^p$ (multiplication by $p$ on exponents) applied to the $j$-series. Then, for $W_1 := \sigma^{-1}(W_0)$: every $a \in A$ maps into $W_1$; every $a \in \mathfrak m_A$ maps into the nonunits of $W_1$; and for every $P \in A[X]$ whose reduction modulo $\mathfrak m_A$ is non-zero, both $P(j)$ and $P(j)^{-1}$ lie in $W_1$.
--
--   This is the assertion that the Frobenius twist $\sigma^{-1}(W_0)$ of the Gauss valuation ring attached to $A$-integral presentations is a branch ring over the $j$-line: it contains $A$, sends $\mathfrak m_A$ into its maximal ideal, and inverts every $A$-polynomial in $j$ with non-zero reduction. It discharges the hypothesis of the dichotomy for valuation rings of $X_0(Mp)$ above $\mathfrak m_A$, and is used in the analysis of the reduction of $X_0(pM)$ in terms of the two $j$-charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_algebraMap_mem_comap_and_forall_aeval_mem_comap_gauss_of_coe_map_eq_qExpand.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.forall_algebraMap_mem_comap_and_forall_aeval_mem_comap_gauss_of_coe_map_eq_qExpand
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) :
    (∀ a : A, algebraMap A ↥K a ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal A,
      algebraMap A ↥K a ∈ (W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom).nonunits) ∧
    (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
      (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) := by sorry
