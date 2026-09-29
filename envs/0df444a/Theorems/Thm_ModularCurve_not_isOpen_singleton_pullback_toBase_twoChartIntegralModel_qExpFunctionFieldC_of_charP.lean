-- Prove2me | Theorems.Thm_ModularCurve_not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
-- name    : ModularCurve.not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/0ad483e9-53e7-56d4-a311-5938a4b4019a
-- title:
--   No isolated points on characteristic-p fibres of the two-chart model
-- statement:
--   Let $p$ be a prime and let $\Gamma\le \mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index containing the translation matrix `ModularGroup.T`. Write $F(\Gamma)=$ [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $\mathbb Q((q))$ obtained by adjoining to $\mathbb Q$ all quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$, where $f,g$ are modular forms of some common weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$ admitting integral $q$-expansions $p_f,p_g\in\mathbb Z[[q]]$ with $\mathrm{intSeriesC}(p_g)\neq 0$. Let $j\in F(\Gamma)$ be nonzero with Laurent series equal to [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15), that is $q^{-1}$ times the image in $\mathbb Q[[q]]$ of the integral power series $E_4^3\cdot\eta^{-24}$-type numerator [`ModularCurve.jNum`](def/ModularCurve_X0.html#L142). Let $\Lambda=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$, and let $\kappa$ be a field of characteristic $p$ that is a $\Lambda$-algebra. Form [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) $\Lambda$ $F(\Gamma)$ $j$, the pushout of the two maps $\operatorname{Spec}$ of the inclusions of the subalgebras `chartAlg` $\Lambda$ $F(\Gamma)$ $\{j\}$ and `chartAlg` $\Lambda$ $F(\Gamma)$ $\{j^{-1}\}$ into the middle chart, with its structure morphism `TwoChartIntegralModel.toBase` to $\operatorname{Spec}\Lambda$, and let $x$ be a point of the fibre product of this morphism with $\operatorname{Spec}$ of $\Lambda\to\kappa$. The assertion is that the singleton $\{x\}$ is not open in the underlying topological space of that fibre product.
--
--   This is the statement that the characteristic-$p$ fibres of the two-chart integral model of the modular function field of $\Gamma$ over $\mathbb Z_{(p)}$ have no isolated points, no hypothesis linking $p$ to the level being imposed, so bad reduction is allowed; it reflects the one-dimensionality of the local rings of the special fibre of a finite normal model. It is used in [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart) to place points of the fibre in a suitable chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped MatrixGroups
open scoped TensorProduct

theorem ModularCurve.not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
    (p : ℕ) [Fact p.Prime]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (j : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)]
    (hj : (j : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]
    (x : ↥(pullback
      (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ))))) :
    ¬ IsOpen ({x} : Set ↥(pullback
      (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ))))) := by sorry
