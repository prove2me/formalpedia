-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/4c5fe70a-a81c-5749-b09b-9150293ea367
-- title:
--   Ogg's modular unit in the j-finite chart algebra
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero, $\zeta \in L$ a primitive $q$-th root of unity admitting a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell)^\times$, and let $K \subseteq L(\!(\mathsf q)\!)$ be the intermediate field generated over $L$ by the coefficientwise image, under $\mathbb{Q} \to L$, of the $q$-expansion function field $\mathtt{xHFunctionField}$ of level $q^2M'$ and group $H_1$. Let $A$ be a henselian discrete valuation domain with fraction field $L$ and algebraically closed residue field, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, with uniformiser $\varpi$, and with an $A$-algebra structure on $K$ compatible with $A \to L \to K$. Let $j \in K$ be nonzero with Laurent series the image of the $j$-expansion $\mathtt{jq}$. Write $C = \mathtt{chartAlgFin}\,A\,K\,j$ for the subalgebra of elements of $K$ integral over $A[j]$. Then there is $g \in C$ whose Laurent series is $\mathtt{qExpand}_q$ applied to the image of $\Delta(\mathsf q)/\Delta(\mathsf q^{q})$, i.e.\ $\Delta(\mathsf q^{q})/\Delta(\mathsf q^{q^2})$, such that $g \neq 0$ in $K$ and $g z = \varpi^k$ in $C$ for some $k \in \mathbb{N}$ and $z \in C$.
--
--   This is the integrality and divisibility statement for Ogg's modular unit $\Delta(\mathsf q^{q})/\Delta(\mathsf q^{q^{2}})$ on the auxiliary level-$H_1$ curve: the unit lies in the chart algebra of elements integral over $A[j]$ and divides a power of the uniformiser there. It is used by [`ModularCurve.FullLevel.AuxLevelOne.exists_labelUnit_chartAlgFin_of_end_blowupChart_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_labelUnit_chartAlgFin_of_end_blowupChart_of_dvd) in the analysis of the two-chart integral model near the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow_of_dvd
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
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (g : ↥(chartAlgFin A (↥K) j)),
      (((g : ↥(chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.qExpand L q (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)) ∧
      ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 ∧
      ∃ (k : ℕ) (z : ↥(chartAlgFin A (↥K) j)), g * z = algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ^ k := by sorry
