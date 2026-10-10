-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_represented_picard_point_cardinality_three_or_five
-- name    : MazurTransfer.order13_actual_represented_picard_point_cardinality_three_or_five
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T00:52:59.9671+00:00
-- url     : https://prove2.me/theorems/2d9f9920-2980-4b3c-9967-bf5d8f73d8b4
-- title:
--   Actual represented Picard points have order 19 over F3 and F5
-- statement:
--   Let $q\in\{3,5\}$, and let $\varepsilon$ be any rational base section of the literal smooth projective order-13 curve $X/\mathbf F_q$. There exists an actual degree-zero Picard designation $D$ representing the normalized algebraically trivial relative Picard functor of $X$ based at $\varepsilon$. Its genuine field-valued point set is finite and
--
--   $$|D(\mathbf F_q)|=19.$$
--
--   The formal conclusion includes both the scheme-map-over-the-base and equivalent over-category descriptions of these points, proving finiteness and cardinality for each. The representing scheme is constructed, rather than supplied as an abstract finite group. The result combines the full arithmetic Picard correspondence with the actual divisor-class cardinalities; rational rank and compatible good reduction remain separate obligations.
-- source:
--   MazurTheorem WIP, pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Generic Picard/divisor geometry reuses official Anthropic FLT, pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Separately checked actual-curve cardinality bridge by Vas and contributors; attribution retained.

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

theorem MazurTransfer.order13_actual_represented_picard_point_cardinality_three_or_five
    (q : ℕ) (hq : q = 3 ∨ q = 5) :
    letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)),
      ∃ (D : RelativePic0Designation (ZMod q)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)))
        (h : RepresentsRelSubPic
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε
          (algEquivZeroCut
            (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q)) ε) D),
        Finite (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) ∧
        Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod q)))) ⟶ Over.mk D.toBase) = 19 ∧
        Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) ∧
        Nat.card (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod q)))) D.toBase) = 19 := by sorry
