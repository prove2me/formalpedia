-- Prove2me | Theorems.Thm_GlobalTheory_FunDescent_res_square_apply
-- name    : GlobalTheory.FunDescent.res_square_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:12.139348+00:00
-- url     : https://prove2.me/theorems/5b68810d-7936-4321-994d-cfc6caebfc06
-- title:
--   Fun Descent: res square apply
-- statement:
--   The Fun Descent construction uses the res square apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L79-L81

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

theorem GlobalTheory.FunDescent.res_square_apply {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) :
    (π ∣_ U).appTop.hom ((res U).hom a) = (res (π ⁻¹ᵁ U)).hom ((π.app U).hom a) := by sorry
