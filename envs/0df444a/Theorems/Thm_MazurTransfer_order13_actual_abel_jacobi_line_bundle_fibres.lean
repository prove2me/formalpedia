-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_abel_jacobi_line_bundle_fibres
-- name    : MazurTransfer.order13_actual_abel_jacobi_line_bundle_fibres
-- status  : Open
-- author  : @Vas
-- created : 2026-10-09T22:41:43.845841+00:00
-- url     : https://prove2.me/theorems/b4c19835-94ad-4a61-871c-969266012508
-- title:
--   Actual order-13 Abel-Jacobi morphism: Poincare fibres are point-difference line bundles
-- statement:
--   Let $C/K$ be the literal order-13 curve over a perfect field with $104\ne0$. For every rational base point $\varepsilon$, construct its represented degree-zero Picard scheme $D$ and an actual morphism $\alpha_\varepsilon:C\to D$, normalized by $\alpha_\varepsilon(\varepsilon)=0$. The scheme is smooth, proper, geometrically connected and abelian. For every field-valued point $p$ over a morphism $t:\operatorname{Spec}L\to\operatorname{Spec}K$, the actual Poincare fibre satisfies
--   \[
--   \mathcal P_{\alpha_\varepsilon(p)}\simeq
--   \mathcal O(p)\otimes\mathcal I(t\varepsilon).
--   \]
--   This is the actual line bundle of the point difference, with the point-divisor and base-point ideal constructed on the actual base-changed curve. The identity holds over every field $L$, without algebraic-closure or rational-point dictionary hypotheses. It supplies the geometric fibre reading needed to identify the arithmetic Picard correspondence with the Abel-Jacobi map.
-- source:
--   Vas and contributors, MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Direct application of its publicly proved full Abel-Jacobi point-divisor pullback theorem to the actual proved geometry and Picard representation. Earlier accepted statements are retained unchanged.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Theorems.Thm_MazurTransfer_order13_actual_picard_abel_jacobi_good_characteristic
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem MazurTransfer.order13_actual_abel_jacobi_line_bundle_fibres.{u}
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0) :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) ∧
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K),
      letI : IsProper (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) :=
        (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).2.2.1
      ∃ (D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K))
        (h : RepresentsRelSubPic
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
          (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D)
        (aj : SchemeHomOver (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) D.toBase),
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
        AbelianSchemePropertyBundle K D.toBase ∧
        ε.1 ≫ aj.1 = D.zeroSection ∧
        ∀ (L : Type u) [Field L]
          (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
          (p : SchemeHomOver t (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)),
          Nonempty ((h.poincare.pullbackAlong
              ⟨p.1 ≫ aj.1, (Category.assoc _ _ _).trans
                ((congrArg (p.1 ≫ ·) aj.2).trans p.2)⟩).L ≅
            (RelEffCartierDiv.ofPoint
              (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) p.1 p.2).lineBundle ⊗
              (RelEffCartierDiv.ofPoint
                (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) (t ≫ ε.1)
                ((Category.assoc _ _ _).trans
                  ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule) := by sorry
