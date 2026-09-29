-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries_unstretched_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries_unstretched_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/2f5f4bc0-78b8-5fc9-836e-685a4a5bef5f
-- title:
--   Fricke relation for the modular unit at width q
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero, $\zeta \in L$ a primitive $q$-th root of unity, and assume some ring homomorphism $\iota : L \to \mathbb{C}$ sends $\zeta$ to $e^{2\pi i/q}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) (the kernel of the unit-group reduction `ZMod.unitsMap` attached to the divisibility `dvd_sq_mul q M'`) with the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$, and let $K \subseteq \mathrm{LaurentSeries}\,L$ be the intermediate field generated over $L$ by the coefficientwise image of the function field [`ModularCurve.xHFunctionField (q^2*M') H₁`](def/ModularCurve_XH.html#L79) of $X_{H_1}$ under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81). Let $A$ be a henselian discrete valuation ring with fraction field $L$, algebraically closed residue field, $q$ in its maximal ideal and $\zeta$ in the image of $A$, with $A$ acting on $K$ compatibly through $L$. Let $x \in K$ have Laurent series the $q$-stretch [`ModularCurve.qExpand L q`](def/ModularCurve_X0.html#L25) of the modular unit series [`ModularCurve.modularUnitSeries q`](def/ModularCurve_ModularUnit.html#L127) $= \Delta/\Delta(q\cdot)$, let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ with $q \mid \delta_{00}$, and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q^2*M') H₁ δ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29): for all weights $k$, all modular forms $f,g$ for $\Gamma_{H_1}(q^2M')$ of weight $k$ with integral $q$-expansions and $g$'s expansion nonzero, and all $y \in K$ whose series is the coefficient image of the quotient of those expansions, the $\iota$-image of the series of $\tau y$ times the width-one $q$-expansion of $g \mid_k \mathrm{conjElemN}\,q\,\delta^{-1}$ equals that of $f \mid_k \mathrm{conjElemN}\,q\,\delta^{-1}$, where $\mathrm{conjElemN}\,q\,\gamma = \begin{pmatrix}\gamma_{00} & \gamma_{01}/q\\ q\gamma_{10} & \gamma_{11}\end{pmatrix}$. Finally let $w \in K$ have Laurent series the unstretched [`ModularCurve.modularUnitSeries q`](def/ModularCurve_ModularUnit.html#L127). Then $\tau x \cdot w = q^{12}$ in $K$.
--
--   This is the Fricke (Atkin–Lehner) relation $w_q\bigl(\Delta(z)/\Delta(qz)\bigr) = q^{12}\,\Delta(qz)/\Delta(z)$ for the modular unit, transported into the function field of $X_{H_1}(q^2M')$ and expressed for the level automorphism attached to a $\Gamma_0(M')$-element $\delta$ with $q \mid \delta_{00}$: the image of the $q$-stretched unit is $q^{12}$ times the inverse of the unstretched one. It feeds the subsequent determination of which coefficients of the transformed unit lie in the maximal ideal of $A$, in the $\Gamma_1(\ell)$-guarded variant of the argument used for small $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries_unstretched_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries_unstretched_of_dvd
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
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ δ⁻¹ K τ)
    (hdvd : (q : ℤ) ∣ (δ 0 0 : ℤ))
    (w : ↥K) (hw : ((w : ↥K) : LaurentSeries L) =
      ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)) :
    τ x * w = algebraMap L ↥K ((q : L) ^ 12) := by sorry
