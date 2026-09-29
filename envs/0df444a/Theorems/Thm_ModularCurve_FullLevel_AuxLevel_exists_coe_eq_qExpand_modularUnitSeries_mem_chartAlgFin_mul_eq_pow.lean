-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow
-- name    : ModularCurve.FullLevel.AuxLevel.exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/12956c0b-2cc4-50f2-adbb-1e73be2f782f
-- title:
--   Ogg's modular unit lies in the j-finite chart algebra
-- statement:
--   Fix primes $q$ and $\ell$ with $q\ge 5$, $\ell\ge 3$, $\ell\ne q$, and a non-zero natural number $M'$ divisible by neither $q$ nor $\ell$. Let $L$ be a field of characteristic $0$ carrying a primitive $(q\ell)$-th root of unity $\xi$, and assume some ring homomorphism $L\to\mathbb{C}$ carries $\xi$ to $\exp(2\pi i/(q\ell))$. Let $K$ be the intermediate field of $L\subseteq L(\!(T)\!)$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb{Q}\to L$ of the function field `xHFunctionFieldC` of level $(q\ell)^2M'$ for the subgroup $H=\ker\bigl((\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times\bigr)$. Let $A$ be a henselian discrete valuation ring with algebraically closed residue field, with $L$ as fraction field, such that $q$ lies in the maximal ideal and $\xi$ is the image of an element of $A$, with uniformiser $\varpi$ (so $\mathfrak{m}_A=(\varpi)$), $K$ an $A$-algebra compatibly with $A\to L\to K$. Let $j\in K$, assumed non-zero, have Laurent series the coefficientwise image of the $q$-expansion $T^{-1}\cdot\,$`jNumQ` of the $j$-invariant. Then there is an element $g$ of `chartAlgFin A K j`, the subalgebra of elements of $K$ integral over $A[j]$, whose Laurent series is the substitution $T\mapsto T^{q\ell}$ applied to the image in $L(\!(T)\!)$ of $\Delta(T)/\Delta(T^q)$, such that $g\ne 0$ in $K$ and $g\cdot z=\varpi^k$ inside the chart algebra for some $k\in\mathbb{N}$ and some $z$ in that algebra.
--
--   This realises Ogg's modular unit $\Delta(w)/\Delta(qw)$ on $X_0(q)$, read at the moduli variable $w=q\ell z$ of the auxiliary level $(q\ell)^2M'$ model, as an element of the integral closure of $A[j]$ in the function field, whose divisor is supported on the fibres over the maximal ideal of $A$ (it divides a power of the uniformiser). It feeds the construction of the distinguished unit used on the $j$-finite chart of the two-chart integral model, via [`ModularCurve.FullLevel.AuxLevel.exists_labelUnit_chartAlgFin_of_end_blowupChart`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_labelUnit_chartAlgFin_of_end_blowupChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow
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
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (g : ↥(chartAlgFin A (↥K) j)),
      (((g : ↥(chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)) ∧
      ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 ∧
      ∃ (k : ℕ) (z : ↥(chartAlgFin A (↥K) j)), g * z = algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ^ k := by sorry
