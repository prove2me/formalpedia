-- Prove2me | Theorems.Thm_GlobalTheory_finRep_exists_isPullback_spec
-- name    : GlobalTheory.finRep_exists_isPullback_spec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:49:46.826989+00:00
-- url     : https://prove2.me/theorems/3c648023-36f8-4abf-b640-4111acbd3349
-- title:
--   Global Theory: fin Rep exists is Pullback spec
-- statement:
--   The Global Theory construction uses the fin Rep exists is Pullback spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinRepExistsIsPullbackSpec.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinRepExistsIsPullbackSpec.lean#L12-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.finRep_exists_isPullback_spec {X Y : Scheme.{0}} (m : X ⟶ Y) [IsFinite m] [Flat m]
    (O : CommRingCat.{0}) (u : Spec O ⟶ Y) :
    ∃ (A : CommRingCat.{0}) (φ : O ⟶ A) (y : Spec A ⟶ X),
      φ.hom.Finite ∧ φ.hom.Flat ∧ IsPullback y (Spec.map φ) m u := by sorry
