-- Prove2me | Theorems.Thm_GlobalTheory_FunDescent_app_injective
-- name    : GlobalTheory.FunDescent.app_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:51.64735+00:00
-- url     : https://prove2.me/theorems/6cc7dd8c-a6b8-46c0-9ee1-c2ae046d0b2e
-- title:
--   Fun Descent: app injective
-- statement:
--   The Fun Descent construction uses the app injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L83-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FunDescent

theorem GlobalTheory.FunDescent.app_injective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] (U : Y.Opens) :
    Function.Injective (π.app U).hom := by sorry
