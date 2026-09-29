-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries
-- name    : ModularCurve.FullLevel.AuxLevel.apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/cb531a18-5ead-5cd7-bf8b-f1d3648b742a
-- title:
--   Ogg's modular unit is fixed when q ∣ δ₁₀
-- statement:
--   Let $q \ge 5$ and $\ell \ge 3$ be primes with $\ell \neq q$, let $M'$ be a nonzero natural number with $q \nmid M'$ and $\ell \nmid M'$, and let $L$ be a field of characteristic $0$ containing a primitive $(q\ell)$-th root of unity $\xi$ for which there is a ring homomorphism $\iota_0 : L \to \mathbb{C}$ with $\iota_0(\xi) = \exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of $L \subset \mathrm{LaurentSeries}\,L$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. $L$ adjoined to the image, under coefficientwise application of $\mathbb{Q} \to L$, of the function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2 M'$ for the subgroup $H =$ [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22) $(q\ell)\,M'$ of $(\mathbb{Z}/(q\ell)^2M')^\times$, namely the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$. Further data: a Henselian discrete valuation ring $A$ with algebraically closed residue field, fraction field $L$, with $q$ in its maximal ideal and $\xi$ in the image of $A$, and an $A$-algebra structure on $K$ compatible with $L$ (these hypotheses are summarised here). Let $x \in K$ have Laurent series $\mathrm{qExpand}_{q\ell}$ of [`ModularCurve.modularUnitSeries`](def/ModularCurve_ModularUnit.html#L127) $q$, i.e. the series $\Delta(\mathsf{q}^{q\ell})/\Delta(\mathsf{q}^{q^2\ell})$, where $\Delta$ is the Laurent series $\mathsf{q}\prod(1-\mathsf{q}^n)^{24}$ with rational coefficients. Let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and satisfy $q \mid \delta_{10}$, and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for $\delta^{-1}$: for every weight $k$, every pair of modular forms $f, g$ of weight $k$ for the group $\Gamma_H((q\ell)^2M')$ inside $\mathrm{GL}_2(\mathbb{R})$ having integral $q$-expansions $p_f, p_g$ with the rational series of $p_g$ nonzero, every $y \in K$ whose Laurent series is the coefficientwise image of that ratio of series, and every $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$, one has $\iota(\tau y) \cdot (g \mid_k \mathrm{conjElemN}_{q\ell}(\delta^{-1}))^\wedge = (f \mid_k \mathrm{conjElemN}_{q\ell}(\delta^{-1}))^\wedge$ as $q$-expansions, where $\mathrm{conjElemN}_m(\gamma)$ is the matrix $\begin{pmatrix} \gamma_{00} & \gamma_{01}/m \\ m\gamma_{10} & \gamma_{11}\end{pmatrix}$. Then $\tau x = x$.
--
--   This is the $\Gamma_0(q)$-invariance of Ogg's modular unit $\Delta(z)/\Delta(qz)$, transported to the auxiliary level $\Gamma_H((q\ell)^2M')$ and to the Galois-theoretic description of the relevant automorphisms: an automorphism attached to $\delta^{-1}$ with $q \mid \delta_{10}$ fixes the element of $K$ whose expansion is that unit. It is used in the computation deciding when the coefficients of the unit's image lie in the maximal ideal of $A$, according to divisibility of $\delta_{10}$ by $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries.lean

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

theorem ModularCurve.FullLevel.AuxLevel.apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries
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
    (hdvd : (q : ℤ) ∣ (δ 1 0 : ℤ)) :
    τ x = x := by sorry
