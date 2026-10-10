-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_picard_abel_jacobi_good_characteristic
-- name    : MazurTransfer.order13_actual_picard_abel_jacobi_good_characteristic
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T18:58:06.551518+00:00
-- url     : https://prove2.me/theorems/6a763a9e-3d2b-4975-973b-a38a4a112b5b
-- title:
--   Actual order-13 curve: represented Picard scheme, commutative group law and pointed Abel-Jacobi morphism in good characteristic
-- statement:
--   For every perfect field K in which 104 is nonzero, the literal two-chart order-13 curve has a rational section. For every such rigidifying section, its degree-zero relative Picard functor is represented by a smooth, proper, geometrically connected scheme equipped with a commutative relative group law and an Abel-Jacobi morphism taking the rigidifying point to the zero section. The section, geometric integrality, arbitrarily large finite maps, Picard representation and group law are derived in the proof. This milestone applies in particular over Q, F_3 and F_5. The divisor-class/Jacobian-point comparison over finite fields and the remaining rational arithmetic are separate, still-open obligations; the full Mazur theorem is unchanged.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Full original finite-map Picard descent and relative group law/Abel-Jacobi proofs from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . All 126 sources in the additional generic dependency closure are natively and fully frontend checked with standard Lean axioms only.

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Free
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finiteMapData_le_isUnit_of_twoAffineOpenCover
import Theorems.Thm_MazurTransfer_order13_actual_section_exists_over_every_field
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_field
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

theorem MazurTransfer.order13_actual_picard_abel_jacobi_good_characteristic.{u}
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0) :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) ∧
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K),
      ∃ (D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K))
        (_ : RepresentsRelSubPic
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
          (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D)
        (L : RelativeGroupLaw K D.toBase)
        (aj : SchemeHomOver (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) D.toBase),
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
        AbelianSchemePropertyBundle K D.toBase ∧
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t D.toBase),
          L.mul t x y = L.mul t y x) ∧
        (L.one (𝟙 (Spec (CommRingCat.of K)))).1 = D.zeroSection ∧
        ε.1 ≫ aj.1 = D.zeroSection := by sorry
