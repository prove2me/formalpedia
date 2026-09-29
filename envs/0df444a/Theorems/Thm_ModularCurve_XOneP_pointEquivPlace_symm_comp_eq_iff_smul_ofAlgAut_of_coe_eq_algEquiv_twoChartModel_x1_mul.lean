-- Prove2me | Theorems.Thm_ModularCurve_XOneP_pointEquivPlace_symm_comp_eq_iff_smul_ofAlgAut_of_coe_eq_algEquiv_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.pointEquivPlace_symm_comp_eq_iff_smul_ofAlgAut_of_coe_eq_algEquiv_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/f5290391-323a-535c-bd63-8ee007e54725
-- title:
--   Transport of j-finite chart points under σ̄
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$, a field $L$ of characteristic zero, an intermediate field $K$ of $L \subseteq \mathrm{LaurentSeries}\,L$, and a discrete valuation domain $A$ with fraction field $L$, equipped with an $A$-algebra structure on $K$ compatible with $A \to L \to K$, together with a nonzero $j \in K$ and $A$-, $L$-algebra structures on $\overline{\mathbb Q}$ forming a scalar tower. Let $M_\eta$ be a `CurveModel` of the field $\overline{\mathbb Q}(X_1(Mp)) =$ `x1FunctionFieldBar (M * p)` (the base change to $\overline{\mathbb Q}$ of the Laurent-series realisation `x1FunctionField (M * p)`) over $\overline{\mathbb Q}$: an integral scheme $M_\eta.C$, proper and smooth of relative dimension $1$ over $\mathrm{Spec}\,\overline{\mathbb Q}$, with a ring isomorphism `ffEquiv` of that field with its function field compatible with the structure map, a bijection of its closed points with the places of the field, matching of stalks with valuation subrings, and every finite set of points contained in an affine open. Let $e_\eta$ be an isomorphism from $M_\eta.C$ to the pullback of the two-chart model map [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) along $\mathrm{Spec}\,\overline{\mathbb Q} \to \mathrm{Spec}\,A$ which is compatible with the structure maps ($h e_\eta$), such that the preimage in $M_\eta.C$ of the $j$-finite chart (the image of $\top$ under [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231), pulled back along $e_\eta$ followed by `pullback.fst`) is nonempty; the hypothesis $hM_\eta\mathrm{pin}$ requires that each element $a$ of the chart algebra `chartAlgFin A K j` $=$ `chartAlg A K {j}`, transported to the function field as the germ at the generic point of its image section and then back along `ffEquiv.symm`, is the Laurent series over $\overline{\mathbb Q}$ obtained from $a \in K \subseteq \mathrm{LaurentSeries}\,L$ by applying $L \to \overline{\mathbb Q}$ coefficientwise, i.e. chart functions are read by their $q$-expansions. Let $\sigma$ be an $L$-algebra automorphism of $K$ and $\bar\sigma$ a $\overline{\mathbb Q}$-algebra automorphism of `x1FunctionFieldBar (M * p)` pinned on $q$-expansions: whenever $f$ has the coefficientwise image of $b \in K$ as Laurent series, $\bar\sigma f$ has that of $\sigma b$; and let $\rho_\sigma$ be a ring automorphism of `chartAlgFin A K j` inducing $\sigma$ on elements of $K$. The conclusion asserts that for every place $P$ of `x1FunctionFieldBar (M * p)` over $\overline{\mathbb Q}$ (a valuation subring, not all of the field, containing the image of $\overline{\mathbb Q}$ and a principal ideal ring) and every ring homomorphism $\psi$ from `chartAlgFin A K j` to $\overline{\mathbb Q}$, the $\overline{\mathbb Q}$-point of $M_\eta.C$ corresponding to $P$ under `Mη.pointEquivPlace.symm`, followed by $e_\eta$ and `pullback.fst`, equals $\mathrm{Spec}(\psi)$ followed by `ιFin` if and only if the point corresponding to the translate $\mathrm{ofAlgAut}(\bar\sigma) \cdot P$ (the action of the semilinear automorphism given by $\bar\sigma$ on the field and the identity on $\overline{\mathbb Q}$) satisfies the same identity with $\psi$ replaced by $\psi \circ \rho_\sigma^{-1}$.
--
--   This is the equivariance, under an automorphism $\sigma$ of $K$ and its $q$-expansion-pinned extension $\bar\sigma$ to $\overline{\mathbb Q}(X_1(Mp))$, of the identification of a generic-fibre point of the two-chart integral model of $X_1(Mp)$ with a ring homomorphism out of the $j$-finite chart algebra: translating a place by $\bar\sigma$ precomposes the associated chart homomorphism with $\rho_\sigma^{-1}$. It is used in the analysis of reduction of points of $X_1(Mp)$ under this action, via [`ModularCurve.XOneP.reducesSnd_iff_gaussReduces_smul_of_gaussReading_algEquiv_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.reducesSnd_iff_gaussReduces_smul_of_gaussReading_algEquiv_twoChartModel_x1_mul) and [`ModularCurve.XOneP.red_eq_red_smul_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.red_eq_red_smul_of_reducesSnd_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_pointEquivPlace_symm_comp_eq_iff_smul_ofAlgAut_of_coe_eq_algEquiv_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.pointEquivPlace_symm_comp_eq_iff_smul_ofAlgAut_of_coe_eq_algEquiv_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (σ : ↥K ≃ₐ[L] ↥K)
    (σbar : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hσbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((σbar f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L))

    (ρσ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρσ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((ρσ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = σ (b : ↥K)) :
    ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
      (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ),
      ((Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) ↔
      ((Mη.pointEquivPlace.symm (SemilinearAut.ofAlgAut σbar • P)).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom (ψ.comp ρσ.symm.toRingHom)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) := by sorry
