-- Prove2me | Theorems.Thm_ModularCurve_XOneP_mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/6604153c-4eb5-5db1-8963-2c7def452240
-- title:
--   Chart functions of X₁(Mp) at ℚ̄-points of the finite chart
-- statement:
--   Fix a prime $p$ and a nonzero $M$, a field $L$ of characteristic $0$, an intermediate field $K$ of the Laurent series field $L((q))$, and a discrete valuation ring $A$ with fraction field $L$, with $A$ acting on $K$ compatibly and with an $A$-algebra structure on $\overline{\mathbb Q}$; fix $j \in K$, $j \neq 0$, and write $R =$ `chartAlgFin A K j` for the $A$-subalgebra of elements of $K$ integral over $A[j]$, with its open immersion `ιFin` into the two-chart model `TwoChartModel A K j` over $\operatorname{Spec} A$. Let $M_\eta$ be a curve model of the intermediate field `x1FunctionFieldBar (M * p)` of $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$, that is, an integral scheme $M_\eta.C$, smooth proper of relative dimension $1$ over $\operatorname{Spec}\overline{\mathbb Q}$, with an isomorphism `ffEquiv` of that field onto its function field compatible with the constants, a bijection between closed points and places, the identification of the image of each closed stalk with the corresponding valuation subring, and the property that finite sets of points lie in affine opens. Let $e_\eta$ be an isomorphism from $M_\eta.C$ onto the base change of the two-chart model along $\operatorname{Spec}\overline{\mathbb Q} \to \operatorname{Spec} A$, commuting with the structure morphisms, and assume the preimage $U$ under $f := e_\eta$ followed by the first projection of the open image of `ιFin` is nonempty. For $r \in R$ let $\hat r$ denote the element of `x1FunctionFieldBar (M * p)` obtained by reading $r$ as a global section of $\operatorname{Spec} R$, transporting it along `ιFin` to the open image of `ιFin`, pulling it back along $f$ to $U$, taking the germ at the generic point, and applying `ffEquiv.symm`. Three assertions are made. First, for every $\overline{\mathbb Q}$-point $x$ of $M_\eta.C$ over $\operatorname{Spec}\overline{\mathbb Q}$ (a section of $M_\eta$.`toBase`) and every ring homomorphism $\psi : R \to \overline{\mathbb Q}$ such that $x$ followed by $f$ equals $\operatorname{Spec}(\psi)$ followed by `ιFin`, and for every $r \in R$: the element $\hat r$ lies in the valuation subring of the place `pointEquivPlace x` attached to $x$, and the evaluation of that place at $\hat r$ (the preimage in $\overline{\mathbb Q}$ of its residue) equals $\psi(r)$. Second, every ring homomorphism $\psi : R \to \overline{\mathbb Q}$ with $\psi \circ (A \to R)$ equal to the structure map $A \to \overline{\mathbb Q}$ arises from such a point $x$. Third, for $a \in A$ the reading $\hat{\,\cdot\,}$ of the image of $a$ in $R$ is the constant, namely the image of $a$ in $\overline{\mathbb Q}$ viewed in `x1FunctionFieldBar (M * p)`.
--
--   This is the dictionary between the affine finite chart of the two-chart model and places of the function field: regular functions on the chart are regular at the place of a $\overline{\mathbb Q}$-point lying in the chart, and their values there are the point's evaluations, with the converse parametrisation of points by $A$-compatible homomorphisms and the normalisation on constants. It is used in the Hecke-correspondence computations on $X_1(Mp)$, where equalities of values of chart functions at images of a place are converted into equalities in $\overline{\mathbb Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
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
    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))] :
    (∀ (x : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _})
        (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ),
      x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      ∀ r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r))))) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
        (Mη.pointEquivPlace x).evalAt
          (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r))))) = ψ r) ∧
    (∀ ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ,
      ψ.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = algebraMap A (AlgebraicClosure ℚ) →
      ∃ x : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _},
        x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) ∧
    (∀ a : A,
      (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a)))))) =
        algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (algebraMap A (AlgebraicClosure ℚ) a)) := by sorry
