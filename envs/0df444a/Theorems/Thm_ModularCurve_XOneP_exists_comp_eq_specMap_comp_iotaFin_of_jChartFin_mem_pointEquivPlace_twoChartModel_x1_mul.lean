-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/906dba95-452c-5847-82e3-ea694cf514a7
-- title:
--   j-integral ℚ̄-points factor through the finite chart
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$; let $L$ be a field of characteristic zero, $K$ an intermediate field of the Laurent series field $L((q))$ over $L$, and $A$ a discrete valuation domain with fraction field $L$, equipped with an algebra structure on $K$ compatible with $A \to L \to K$, and also with an algebra structure on $\overline{\mathbb{Q}}$; let $j \in K$ be nonzero. Let $M\eta$ be a curve model over $\overline{\mathbb{Q}}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182), the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the $q$-expansion field of $X_1(Mp)$ over $\mathbb{Q}$; that is, an integral scheme $M\eta.C$ with a proper, smooth relative dimension one morphism `toBase` to $\operatorname{Spec} \overline{\mathbb{Q}}$, a ring isomorphism `ffEquiv` of that field with the function field of $M\eta.C$ over the base, a bijection `placeOfPoint` from closed points to places of the field over $\overline{\mathbb{Q}}$ (valuation subrings, proper, containing $\overline{\mathbb{Q}}$, with principal ideals) matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open. Let $e\eta$ be an isomorphism from $M\eta.C$ to the fibre product of the structure morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) of the two-chart model (the pushout of the finite and pole charts over $\operatorname{Spec} A$) with $\operatorname{Spec}$ of $A \to \overline{\mathbb{Q}}$, compatible with the two structure morphisms, and write $\Phi = e\eta$ followed by the first projection; assume the preimage under $\Phi$ of the open image of the finite chart immersion [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231) is nonempty. Let $x$ be a $\overline{\mathbb{Q}}$-point of $M\eta.C$, i.e. a section of `toBase`, and assume that the element of the function field obtained by pulling back along $\Phi$ the global section $j$ of the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) (the subalgebra of elements of $K$ integral over $A[j]$) and taking its germ at the generic point lies, via `ffEquiv.symm`, in the valuation subring of the place attached to $x$ by `pointEquivPlace`. Then there is a ring homomorphism $\psi$ from `chartAlgFin A K j` to $\overline{\mathbb{Q}}$ such that $x$ followed by $\Phi$ equals $\operatorname{Spec} \psi$ followed by `ιFin`.
--
--   The statement says that a $\overline{\mathbb{Q}}$-point of the geometric generic fibre of the two-chart model at which the chart function $j$ is regular is not a pole of $j$, hence lies in the $j$-finite affine chart, and that such a point is given by a ring homomorphism from the finite chart algebra to $\overline{\mathbb{Q}}$. It is the form in which the chart-membership criterion is used in the analysis of Hecke correspondences on the model of $X_1(Mp)$ and of their reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)
    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (x : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _})
    (hjx : (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv (ModularCurve.TwoChart.jChartFin A (↥K) j)))))) ∈ (Mη.pointEquivPlace x).toValuationSubring) :
    ∃ ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ,
      x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by sorry
