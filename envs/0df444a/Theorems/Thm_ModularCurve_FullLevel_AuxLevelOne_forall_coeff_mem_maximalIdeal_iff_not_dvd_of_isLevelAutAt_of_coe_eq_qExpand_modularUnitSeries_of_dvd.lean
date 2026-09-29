-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/58317686-cb81-5126-8f4d-9b479a72774d
-- title:
--   Coefficients of τ x lie in mathfrak m_A iff q∤δ₁₀
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and $\ell$ a prime with $\ell\equiv 11\pmod{12}$ and $\ell\mid M'$. Let $L$ be a field of characteristic zero, $\zeta\in L$ a primitive $q$-th root of unity, and assume there is a ring homomorphism $\iota_0:L\to\mathbb C$ with $\iota_0(\zeta)=e^{2\pi i/q}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$ with the kernel of reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/\ell)^\times$, and let $K$ be the intermediate field of $L\subseteq L((\mathsf q))$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ over $\mathbb Q$. Let $A$ be a Henselian discrete valuation domain with algebraically closed residue field, with fraction field $L$, with $q\in\mathfrak m_A$ and $\zeta$ in the image of $A$, and with $K$ an $A$-algebra compatibly with $L$. Let $x\in K$ have Laurent series the $q$-stretch ($\mathsf q\mapsto\mathsf q^q$) of the image in $L((\mathsf q))$ of $\Delta/\Delta(\mathsf q^q)$, let $\delta\in\Gamma_0(M')\subseteq\mathrm{SL}_2(\mathbb Z)$, and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ δ⁻¹ K τ`, i.e.: for every weight $k$, all modular forms $f,g$ for $\Gamma_{H_1}(q^2M')$ of weight $k$ admitting integral $q$-expansions given by power series $p_f,p_g$ over $\mathbb Z$ with $p_g\neq 0$ in $L((\mathsf q))$, every $y\in K$ whose Laurent series is the image of $p_f/p_g$, and every $\iota:L\to\mathbb C$ with $\iota(\zeta)=e^{2\pi i/q}$, one has $\iota(\tau y)\cdot(g\mid_k \delta^{-1}_{(q)})^{\wedge}=(f\mid_k \delta^{-1}_{(q)})^{\wedge}$ on $q$-expansions at $1$, where $\delta^{-1}_{(q)}$ denotes the conjugated matrix $\begin{pmatrix}a&b/q\\ qc&d\end{pmatrix}$ attached to $\delta^{-1}$. Then every Laurent coefficient of $\tau x$ lies in the image of $\mathfrak m_A$ under $A\to L$ if and only if $q$ does not divide the lower-left entry $\delta_{10}$.
--
--   The statement records the reduction behaviour of the modular unit $\Delta(\mathsf q^{q})/\Delta(\mathsf q^{q^2})$ under the Galois automorphism attached to $\delta^{-1}$: whether its $\mathsf q$-expansion becomes identically zero modulo the maximal ideal is decided by the divisibility of the lower-left entry of $\delta$ by $q$, which distinguishes the two Igusa components of the reduction. This version works with the auxiliary level $H_1$ cut out by the congruence conditions modulo $q$ and modulo a guard prime $\ell\equiv 11\pmod{12}$, and is used in the construction of a label unit on the finite chart of the blown-up two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries_of_dvd
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
    (x : ↥K) (hx : ((x : ↥K) : LaurentSeries L) =
      ModularCurve.qExpand L q (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)))
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ δ⁻¹ K τ) :
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((τ x : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ↔
      ¬ ((q : ℤ) ∣ (δ 1 0 : ℤ)) := by sorry
