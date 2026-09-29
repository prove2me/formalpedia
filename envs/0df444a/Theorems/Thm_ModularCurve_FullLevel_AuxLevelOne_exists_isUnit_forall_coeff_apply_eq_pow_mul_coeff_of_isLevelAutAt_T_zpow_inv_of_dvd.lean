-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isUnit_forall_coeff_apply_eq_pow_mul_coeff_of_isLevelAutAt_T_zpow_inv_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_isUnit_forall_coeff_apply_eq_pow_mul_coeff_of_isLevelAutAt_T_zpow_inv_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/56c1bd73-8159-536f-a08a-fc7a016dbb8f
-- title:
--   Level automorphism at (T^s)⁻¹ scales Laurent coefficients geometrically
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$, and assume some ring homomorphism $L \to \mathbb{C}$ carries $\zeta$ to $\exp(2\pi i/q)$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell)^\times$, and let $K \subseteq \operatorname{LaurentSeries} L$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image of the rational $q$-expansion function field of $\Gamma_{H_1}(q^2M')$. Let $A$ be a discrete valuation domain with fraction field $L$, henselian with algebraically closed residue field, with $q$ in its maximal ideal and $\zeta$ in the image of $A$, and let $K$ be an $A$-algebra compatibly with $L$. Finally let $s \in \mathbb{Z}$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ (ModularGroup.T ^ s)⁻¹ K τ`: for every weight $k$, every pair $f,g$ of modular forms of weight $k$ for $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f,p_g \in \mathbb{Z}[[X]]$ and $p_g$ not mapping to $0$ over $\mathbb{Q}$, every $x \in K$ whose Laurent series is the coefficientwise image in $L$ of the quotient of those rational series, and every $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = \exp(2\pi i/q)$, one has $\iota(\tau x) \cdot (g\mid_k \gamma')^{\wedge} = (f\mid_k \gamma')^{\wedge}$ as $q$-expansions at $1$, where $\gamma'$ is the matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ attached to $(T^s)^{-1} = \begin{pmatrix} a& b\\ c&d\end{pmatrix}$. The conclusion: there is a unit $u \in A$ such that for all $w \in K$ and all $n \in \mathbb{Z}$, the $n$-th Laurent coefficient of $\tau w$ equals $(\text{image of } u \text{ in } L)^n$ times the $n$-th Laurent coefficient of $w$.
--
--   This is the integral form of the classical effect of the translation $\tau \mapsto \tau + s$ on $q$-expansions: the automorphism of the function field attached to $(T^s)^{-1}$ multiplies the $n$-th coefficient by the $n$-th power of a fixed root of unity, here realised as a unit of the henselian discrete valuation ring $A$. It is used in the $\Gamma_1(\ell)$ auxiliary-level analysis, where it feeds the criterion [`ModularCurve.FullLevel.AuxLevelOne.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries_of_dvd) for divisibility of the coefficients of modular unit series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isUnit_forall_coeff_apply_eq_pow_mul_coeff_of_isLevelAutAt_T_zpow_inv_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.exists_isUnit_forall_coeff_apply_eq_pow_mul_coeff_of_isLevelAutAt_T_zpow_inv_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (s : ℤ)
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ (ModularGroup.T ^ s)⁻¹ K τ) :
    ∃ u : A, IsUnit u ∧ ∀ (w : ↥K) (n : ℤ),
      ((τ w : ↥K) : LaurentSeries L).coeff n = (algebraMap A L u) ^ n * ((w : ↥K) : LaurentSeries L).coeff n := by sorry
