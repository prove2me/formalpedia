-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries
-- name    : ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/8b715aa1-8702-52d7-a8b3-a87ea0ee6a7f
-- title:
--   Translates of the modular unit: coefficients in mathfrak m_A iff q∤δ₁₀
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\ne q$, and let $M'$ be a nonzero natural number divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell)$-th root of unity, and assume some ring homomorphism $\iota_0:L\to\mathbb C$ sends $\xi$ to $e^{2\pi i/(q\ell)}$. Let $K$ be the intermediate field of $L\subseteq L((\mathsf q))$ obtained as `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image of the $\mathbb Q$-function field `xHFunctionField` of level $N_0=(q\ell)^2M'$ and subgroup $H=$ `levelH` $(q\ell)\,M'$, the kernel of the reduction $(\mathbb Z/N_0)^\times\to(\mathbb Z/q\ell)^\times$ (units congruent to $1$ modulo $q\ell$); the relevant congruence group is the image in $\mathrm{SL}_2(\mathbb Z)$ of the elements of $\Gamma_0(N_0)$ whose associated unit lies in $H$. Let $A$ be a Henselian discrete valuation ring with algebraically closed residue field, with fraction field $L$, such that $q\in\mathfrak m_A$ and $\xi$ lies in the image of $A$, and let $K$ be an $A$-algebra compatibly with $L$. Let $x\in K$ have Laurent series $\mathrm{qExpand}_{q\ell}$ applied to the coefficient image of `modularUnitSeries` $q$, that is $\Delta(\mathsf q^{q\ell})/\Delta(\mathsf q^{q^2\ell})$. Let $\delta\in\Gamma_0(M')\subseteq\mathrm{SL}_2(\mathbb Z)$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for $\delta^{-1}$, scaling parameter $q\ell$, root of unity $\xi$ and level $(N_0,H)$: for all weights $k$, all modular forms $f,g$ of that level with integral $q$-expansions and $g\ne 0$, and all $y\in K$ whose Laurent series is the quotient of those $q$-expansions, the complex specialisation of $\tau y$ along any $\iota$ with $\iota\xi=e^{2\pi i/(q\ell)}$ times the $q$-expansion of $g\mid_k \mathrm{conjElemN}_{q\ell}(\delta^{-1})$ equals the $q$-expansion of $f\mid_k \mathrm{conjElemN}_{q\ell}(\delta^{-1})$. Then every Laurent coefficient of $\tau x$ lies in the image of $\mathfrak m_A$ in $L$ if and only if $q$ does not divide the lower-left entry $\delta_{10}$.
--
--   This is the arithmetic heart of the auxiliary-level construction: in the Deligne–Rapoport picture of $X_0(q)$ modulo $q$, the modular unit $\Delta(w)/\Delta(qw)$ is invertible on the component through the cusp $\infty$ and vanishes on the other component, and the statement transports this dichotomy to full level, the component being recorded by the residue class of the lower-left entry of $\delta\in\Gamma_0(M')$. It is used in the construction of a label unit on the finite chart of the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries.lean

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

theorem ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries
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
          (ModularCurve.FullLevel.levelH (q * ℓ) M') δ⁻¹ K τ) :
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((τ x : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ↔
      ¬ ((q : ℤ) ∣ (δ 1 0 : ℤ)) := by sorry
