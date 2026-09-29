-- Prove2me | Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
-- name    : ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/9a23f776-7c23-5099-a59c-b7d23c00feca
-- title:
--   Chart functions of the two-chart model have ℤ₍ₚ₎-integral q-expansions
-- statement:
--   Let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbf Z)$ and let $p$ be a prime. Write $F =$ `qExpFunctionFieldC ℚ Γ` for the intermediate field of $\mathbf Q((q))$ obtained by adjoining to $\mathbf Q$ the set of quotients $\mathrm{intSeriesC}\,p_f / \mathrm{intSeriesC}\,p_g$, where $f,g$ run over the modular forms of one and the same weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbf R)$ admitting integral $q$-expansions $p_f, p_g \in \mathbf Z[[q]]$ with $\mathrm{intSeriesC}\,p_g \neq 0$. Let $j \in F$ be nonzero and assume that, as a Laurent series, $j$ equals `jqModC ℚ`, that is $q^{-1}$ times the power series $E_4^3 \cdot \mathrm{dedekindEtaUnitInv}$ with coefficients mapped from $\mathbf Z$ to $\mathbf Q$. Let $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) be the subring of $\mathbf Q$ of rationals whose denominator is coprime to $p$, i.e. $\mathbf Z_{(p)}$. The conclusion is a conjunction of two assertions of the same shape, for the two chart algebras of the two-chart integral model: first, every element $b$ of `TwoChartIntegralModel.chartAlgFin R F j`, the $R$-subalgebra of $F$ of elements integral over $R[j]$, is of the form $b =$ `coeffMap (algebraMap R ℚ) y` for some Laurent series $y$ over $R$; second, the same holds for every element of `TwoChartIntegralModel.chartAlgInf R F j`, the elements of $F$ integral over $R[j^{-1}]$. Equivalently, all $q$-expansion coefficients of a chart function lie in $\mathbf Z_{(p)}$. Only the chart algebras occur; the pushout scheme [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) itself is not mentioned.
--
--   This is the integrality half of the $q$-expansion principle for the two-chart (Kroneckerian) model of $X(\Gamma)$ over $\mathbf Z_{(p)}$: functions on either affine chart have $p$-integral $q$-expansions, by a Gauss-valuation argument on the bounded-denominator Laurent series representing elements of $F(\Gamma)$. It feeds the constructions of ring homomorphisms from the chart algebras into $\mathbf Z_{(p)}((q))$ used in the study of the reduction of modular curves of $\Gamma_H$-level, and is cited by the results on fibre maps and retractions at such levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ) :
    (∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        ∃ y : LaurentSeries ↥(GaloisRep.ratLocalizedAt p),
          coeffMap (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) ∧
    (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        ∃ y : LaurentSeries ↥(GaloisRep.ratLocalizedAt p),
          coeffMap (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) := by sorry
