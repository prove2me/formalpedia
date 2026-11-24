-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_lift_sqMap
-- name    : GlobalTheory.AbLaw.CubeOpen.lift_sqMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:05.303032+00:00
-- url     : https://prove2.me/theorems/b06172a1-664e-472a-b237-a7eca0b404fc
-- title:
--   Cube Open: lift sq Map
-- statement:
--   The Cube Open construction uses the lift sq Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivBasicOpenOfTrivFibre.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivBasicOpenOfTrivFibre.lean#L136-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S)

theorem GlobalTheory.AbLaw.CubeOpen.lift_sqMap (a b : A ⟶ A) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ sqMap φ A =
      pullback.fst A.hom φ ≫ (lift a b).left := by sorry
