-- Prove2me | Theorems.Thm_MazurTransfer_order13_every_actual_represented_picard_point_cardinality_three_or_five
-- name    : MazurTransfer.order13_every_actual_represented_picard_point_cardinality_three_or_five
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T01:09:37.104994+00:00
-- url     : https://prove2.me/theorems/1ba9032d-5d29-4d85-935c-97ebdd5ae474
-- title:
--   Every actual representing Picard model has 19 field-valued points over F3 and F5
-- statement:
--   Let $q\in\{3,5\}$ and let $\varepsilon$ be any rational base section of the literal order-13 curve $X/\mathbf F_q$. Let $D$ be any actual designation representing the normalized degree-zero relative Picard functor of $X$ based at $\varepsilon$, with its full universal Poincare-family property. Then its field-valued point set is finite and
--
--   $$|D(\mathbf F_q)|=19.$$
--
--   The conclusion covers every representing model and proves both finiteness and cardinality for the scheme-map-over-the-base and equivalent over-category descriptions. The full representation property is the explicit hypothesis; no finite point set or cardinality is supplied. Actual existence of such a representation and its point count are separately proved in the dependency theorem. Universality transfers this count to a model chosen for compatible good reduction.
-- source:
--   MazurTheorem WIP, pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . The full relative Picard interface reuses official Anthropic FLT, pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Separately checked universality and actual-model point-count transfer by Vas and contributors; source attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem MazurTransfer.order13_every_actual_represented_picard_point_cardinality_three_or_five
    (q : ℕ) (hq : q = 3 ∨ q = 5) :
    letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
    ∀ (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)))
      (D : RelativePic0Designation (ZMod q)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)))
      (h : RepresentsRelSubPic
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε
        (algEquivZeroCut
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε) D),
      Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) ∧
      Nat.card (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) = 19 ∧
      Finite (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) ∧
      Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) = 19 := by sorry
