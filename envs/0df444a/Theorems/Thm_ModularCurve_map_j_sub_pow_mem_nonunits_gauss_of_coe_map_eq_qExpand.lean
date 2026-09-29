-- Prove2me | Theorems.Thm_ModularCurve_map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand
-- name    : ModularCurve.map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/5ddadec0-4eae-5575-9b14-f68ffdc1a0ca
-- title:
--   Kronecker's congruence read in the Gauss valuation ring
-- statement:
--   Fix a prime $p$, a field $L$ of characteristic zero, an intermediate field $K$ of the Laurent series field $L((q))$ over $L$, and a discrete valuation ring $A$ which is a domain with fraction field $L$ and such that $p$ lies in the maximal ideal of $A$; $K$ is moreover an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be an element whose image in $L((q))$ is the coefficientwise image along $\mathbb{Q} \to L$ of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), that is of $q^{-1}J(q)$ where $J$ is the integral numerator power series of the $j$-invariant viewed over $\mathbb{Q}$. Let $W_0$ be a valuation subring of $K$ whose elements are characterised as those $f$ admitting a presentation $f \cdot \tilde y = \tilde x$ in $L((q))$, with $x, y$ power series over $A$, $\tilde x, \tilde y$ their images under $A \to L$ followed by the inclusion of power series into Laurent series, and the reduction of $y$ modulo the maximal ideal of $A$ nonzero. Let $\sigma$ be an $L$-algebra automorphism of $K$ with $\sigma(j)$ mapping to the coefficientwise image of the Laurent series obtained from [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) by multiplying all exponents by $p$ (substitution $q \mapsto q^p$). Then $j \in W_0$ and $\sigma(j) - j^p$ is a nonunit of $W_0$.
--
--   This is Kronecker's congruence $j(q^p) \equiv j(q)^p \pmod p$, read in the Gauss valuation ring $W_0$ of $K$ attached to $A$: the difference $\sigma(j) - j^p$ lies in the maximal ideal of $W_0$. It feeds the analysis of the special fibre of the modular curves at $p$, being used in the identification of the two sheets and in the Frobenius obstruction computations for $X_0(pM)$ and $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand
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
    j ∈ W₀ ∧ σ j - j ^ p ∈ W₀.nonunits := by sorry
