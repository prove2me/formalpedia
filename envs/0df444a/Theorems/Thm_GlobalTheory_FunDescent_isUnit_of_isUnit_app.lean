-- Prove2me | Theorems.Thm_GlobalTheory_FunDescent_isUnit_of_isUnit_app
-- name    : GlobalTheory.FunDescent.isUnit_of_isUnit_app
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:08.54767+00:00
-- url     : https://prove2.me/theorems/c767a63e-26fb-4b09-b368-e95694b87c84
-- title:
--   Fun Descent: is Unit of is Unit app
-- statement:
--   The Fun Descent construction uses the is Unit of is Unit app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L92-L100

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

theorem GlobalTheory.FunDescent.isUnit_of_isUnit_app {X Y : Scheme.{0}} (π : X ⟶ Y) [Surjective π] (U : Y.Opens)
    (a : Γ(Y, U)) (ha : IsUnit ((π.app U).hom a)) : IsUnit a := by sorry
