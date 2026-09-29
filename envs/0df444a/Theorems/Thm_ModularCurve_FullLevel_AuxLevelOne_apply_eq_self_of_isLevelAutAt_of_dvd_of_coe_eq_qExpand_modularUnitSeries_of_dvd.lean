-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/6e90fdeb-0653-59f9-9585-3fb36dcc490c
-- title:
--   Ogg's modular unit is fixed by level automorphisms over Γ₀(q)
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number with $q \nmid M'$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$, and assume there is a ring homomorphism $\iota_0 : L \to \mathbb{C}$ with $\iota_0(\zeta) = e^{2\pi i/q}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell)^\times$, and let $K \subseteq \mathrm{LaurentSeries}\,L$ be the intermediate field generated over $L$ by the coefficientwise image of the rational function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q^2M', H_1)$. Let $A$ be a Henselian discrete valuation domain with algebraically closed residue field, with fraction field $L$, such that $q$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, together with an $A$-algebra structure on $K$ compatible with that of $L$. Let $x \in K$ have Laurent series $\mathrm{qExpand}_q$ applied to the coefficient image of [`ModularCurve.modularUnitSeries`](def/ModularCurve_ModularUnit.html#L127) $q$, i.e. the series $\Delta(\mathsf q^{q})/\Delta(\mathsf q^{q^2})$ obtained from $\Delta \cdot (\Delta \circ \mathsf q \mapsto \mathsf q^{q})^{-1}$. Let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ with $q \mid \delta_{10}$, and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for the data $(q, \zeta, q, q^2M', H_1, \delta^{-1})$: for all weights $k$, all modular forms $f, g$ of weight $k$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ attached to $\Gamma_{H_1}(q^2M')$ having integral $q$-expansions $p_f, p_g$ with the rational series of $p_g$ nonzero, all $y \in K$ whose Laurent series is the coefficient image of $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$, and all $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the coefficientwise image under $\iota$ of $\tau(y)$ times the $q$-expansion of $g \mid_k \mathrm{conjElemN}_q(\delta^{-1})$ equals the $q$-expansion of $f \mid_k \mathrm{conjElemN}_q(\delta^{-1})$, where $\mathrm{conjElemN}_m(\gamma) = \begin{pmatrix} \gamma_{00} & \gamma_{01}/m \\ m\gamma_{10} & \gamma_{11}\end{pmatrix}$. Then $\tau(x) = x$.
--
--   This is the formal counterpart of the classical observation that $\Delta(z)/\Delta(qz)$ is a modular unit invariant for $\Gamma_0(q)$: the level automorphism attached to an element $\delta$ of $\Gamma_0(M')$ whose lower-left entry is divisible by $q$ fixes the element of $K$ carrying that $q$-expansion. It is used in the companion result identifying, in terms of divisibility by $q$, which Laurent coefficients of the unit lie in the maximal ideal of $A$, in the $\Gamma_1(\ell)$-guard variant of the auxiliary-level analysis of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries_of_dvd
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
    (hdvd : (q : ℤ) ∣ (δ 1 0 : ℤ)) :
    τ x = x := by sorry
