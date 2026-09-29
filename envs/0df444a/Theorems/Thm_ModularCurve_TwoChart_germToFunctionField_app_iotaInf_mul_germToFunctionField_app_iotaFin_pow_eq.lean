-- Prove2me | Theorems.Thm_ModularCurve_TwoChart_germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq
-- name    : ModularCurve.TwoChart.germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/600ceb9d-3391-50d0-a981-0a175bb3bdd6
-- title:
--   Reading b'jⁿ=a in the function field of Z
-- statement:
--   Let $A$ be a commutative ring, $K$ a field with an $A$-algebra structure, and $j \in K$ a nonzero element. Write $\mathcal O_{\mathrm{fin}} =$ `chartAlgFin A K j` for the $A$-subalgebra of $K$ of elements integral over $A[j]$, and $\mathcal O_\infty =$ `chartAlgInf A K j` for the $A$-subalgebra of elements integral over $A[j^{-1}]$; let $\mathfrak X =$ [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) be the pushout of the two morphisms $\operatorname{Spec}$ of the common overlap algebra $\to \operatorname{Spec}\mathcal O_{\mathrm{fin}}$, $\operatorname{Spec}\mathcal O_\infty$ induced by the inclusions, with chart morphisms `ιFin A K j` and `ιInf A K j` into $\mathfrak X$, whose `appIso` at $\top$ identifies sections of $\mathfrak X$ over the open image of each chart with the corresponding chart algebra. Let $Z$ be an integral scheme and $h \colon Z \to \mathfrak X$ a morphism such that the preimages under $h$ of the open images of `ιFin A K j` and of `ιInf A K j` are both nonempty, so that each carries a germ map to the function field $K(Z)$ at the generic point of $Z$. For $b' \in \mathcal O_\infty$, $a \in \mathcal O_{\mathrm{fin}}$ and $n \in \mathbb N$ with $b' j^n = a$ in $K$, the germ in $K(Z)$ of the pullback along $h$ of the section $b'$ over the infinite chart, multiplied by the $n$-th power of the germ of the pullback of the section $j$ (that is, `jChartFin A K j`) over the finite chart, equals the germ of the pullback of the section $a$ over the finite chart.
--
--   This is the bookkeeping step that transfers a multiplicative relation $b'j^n = a$ holding in $K$ between sections of the two chart algebras into the corresponding identity between their germs at the generic point of an integral scheme $Z$ mapping to the two-chart model, the point being that both chart readings factor through the stalk at the image of the generic point, which lies in the overlap of the two charts. It is used in the computation identifying readings of chart coordinates at $Z$-points of the two-chart model in the study of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_TwoChart_germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem ModularCurve.TwoChart.germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    {Z : Scheme.{u}} [AlgebraicGeometry.IsIntegral Z] (h : Z ⟶ ModularCurve.TwoChartModel A K j)
    [Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)))]
    (b' : ↥(ModularCurve.TwoChart.chartAlgInf A K j)) (a : ↥(ModularCurve.TwoChart.chartAlgFin A K j)) (n : ℕ) (hab : (b' : K) * j ^ n = (a : K)) :
    (Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιInf A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgInf A K j))).inv b'))) *
      ((Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A K j))).inv (ModularCurve.TwoChart.jChartFin A K j))))) ^ n =
      (Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A K j))).inv a))) := by sorry
