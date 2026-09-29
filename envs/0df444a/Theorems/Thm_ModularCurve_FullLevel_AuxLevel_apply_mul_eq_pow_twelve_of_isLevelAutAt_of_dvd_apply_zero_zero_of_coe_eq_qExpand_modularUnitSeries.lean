-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries
-- name    : ModularCurve.FullLevel.AuxLevel.apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/b62235a2-82ce-5426-8863-57b31e97f95b
-- title:
--   Fricke-type relation τ(x) w=q¹² in the Borel case
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, and let $M'$ be a nonzero natural number divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic zero containing a primitive $(q\ell)$-th root of unity $\xi$, and assume there is a ring homomorphism $\iota\colon L\to\mathbb C$ with $\iota(\xi)=\exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image of the function field `xHFunctionField` of level $(q\ell)^2M'$ and group `levelH` $(q\ell)\,M'$, the latter being the kernel of the reduction $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$. Let $A$ be a henselian discrete valuation ring with algebraically closed residue field, a subring of $L$ with fraction field $L$, such that $q$ lies in the maximal ideal of $A$ and $\xi$ lies in the image of $A$, together with a compatible $A$-algebra structure on $K$. Let $x\in K$ have Laurent series $\mathrm{qExpand}_{q\ell}$ of the coefficientwise image of `modularUnitSeries` $q$, that is $\Delta(\mathsf q^{\,q\ell})/\Delta(\mathsf q^{\,q^2\ell})$ where `deltaSeries` is the Laurent series $\mathsf q\cdot(\text{Dedekind }\eta\text{-unit})$. Let $\delta\in\mathrm{SL}_2(\mathbb Z)$ lie in $\Gamma_0(M')$ with $q\mid\delta_{00}$, and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for $L$, $q\ell$, $\xi$, $q\ell$, $(q\ell)^2M'$, `levelH` $(q\ell)\,M'$ and $\delta^{-1}$: for all weights $k$, all modular forms $f,g$ of weight $k$ for `GammaH` $((q\ell)^2M')$ `levelH` with integral $q$-expansions $p_f,p_g$ ($p_g$ with nonzero associated series), any $y\in K$ whose Laurent series is the coefficientwise image of $p_f/p_g$, and any embedding $\iota$ sending $\xi$ to $\exp(2\pi i/(q\ell))$, the $\iota$-image of $\tau(y)$ times the $q$-expansion of $g\mid_k\mathrm{conjElemN}(q\ell,\delta^{-1})$ equals the $q$-expansion of $f\mid_k\mathrm{conjElemN}(q\ell,\delta^{-1})$, where $\mathrm{conjElemN}(m,\gamma)=\begin{pmatrix}\gamma_{00}&\gamma_{01}/m\\ m\gamma_{10}&\gamma_{11}\end{pmatrix}$. Finally let $w\in K$ have Laurent series $\mathrm{qExpand}_{\ell}$ of the same modular unit series, namely $\Delta(\mathsf q^{\,\ell})/\Delta(\mathsf q^{\,q\ell})$. Then $\tau(x)\,w$ equals the image in $K$ of $q^{12}\in L$.
--
--   This is the Fricke-involution case of the computation of the Galois action on the modular unit $\Delta(z)/\Delta(qz)$: when the Borel condition $q\mid\delta_{00}$ holds, the coset $\Gamma_0(q)\delta^{-1}$ is that of $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$, and the relation $w_q(\Delta(z)/\Delta(qz))=q^{12}\Delta(qz)/\Delta(z)$ of Ogg yields the stated product $q^{12}$. It feeds the valuation-theoretic criterion [`ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries`](thm.html#ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries), which distinguishes the Borel from the non-Borel case by whether the coefficients of the transformed unit lie in the maximal ideal of $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries.lean

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

theorem ModularCurve.FullLevel.AuxLevel.apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (x : ↥K) (hx : ((x : ↥K) : LaurentSeries L) =
      ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)))
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') δ⁻¹ K τ)
    (hdvd : (q : ℤ) ∣ (δ 0 0 : ℤ))
    (w : ↥K) (hw : ((w : ↥K) : LaurentSeries L) =
      ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q))) :
    τ x * w = algebraMap L ↥K ((q : L) ^ 12) := by sorry
