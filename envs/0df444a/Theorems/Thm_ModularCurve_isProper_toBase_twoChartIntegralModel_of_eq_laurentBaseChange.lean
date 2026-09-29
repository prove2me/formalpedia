-- Prove2me | Theorems.Thm_ModularCurve_isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
-- name    : ModularCurve.isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/61753a71-6b91-5d79-b614-ea9f5714365f
-- title:
--   Properness of the two-chart integral j-model over A
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$ containing `ModularGroup.T`, let $L$ be a field of characteristic zero, and let $K$ be an intermediate field of $L \subseteq L((q))$ (Laurent series over $L$) which is assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)`](def/ModularCurve_LaurentCoeff.html#L103): the subfield of $L((q))$ generated over $L$ by the image, under the coefficientwise ring map `coeffEmb L : LaurentSeries ℚ → LaurentSeries L` induced by $\mathbb Q \to L$, of the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the ratios `intSeriesC ℚ pf / intSeriesC ℚ pg` attached to integral $q$-expansions $pf,pg$ of modular forms of a common weight for $\Gamma$ (with the denominator nonzero). Let $A$ be a Noetherian unique factorisation domain together with an algebra structure making $L$ its fraction field and an $A$-algebra structure on $K$ compatible with $A \to L \to K$. Let $j \in K$ be nonzero with image in $L((q))$ equal to `coeffEmb L ModularCurve.jq`, where `jq` is $q^{-1}$ times the power series `jNumQ` over $\mathbb Q$. Then the morphism [`AlgebraicCurve.TwoChartIntegralModel.toBase A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) from the two-chart integral model — the pushout of the two maps $\operatorname{Spec}$ of the inclusions of `chartAlg A K {j}` and `chartAlg A K {j⁻¹}` into the middle chart algebra — to $\operatorname{Spec} A$ is proper.
--
--   This provides the properness half of the statement that the two-chart integral model of the function field of the modular curve attached to $\Gamma$, taken with respect to $j$, is a proper curve over an arbitrary Noetherian factorial base with fraction field $L$; classically it is the properness of the normalisation of the $j$-line in the compactified coarse moduli scheme. It is used in the construction and study of integral models of $X_1(Mp)$ over the relevant discrete valuation rings, in particular in the results on their special fibres, Picard groups and Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry

theorem ModularCurve.isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A]
    [Algebra A L] [IsFractionRing A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    IsProper (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) := by sorry
