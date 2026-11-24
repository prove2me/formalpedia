-- Prove2me | Theorems.Thm_GlobalTheory_FunDescent_res_square
-- name    : GlobalTheory.FunDescent.res_square
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:46.660046+00:00
-- url     : https://prove2.me/theorems/33a97f9b-eb9f-434d-946a-035e5245f154
-- title:
--   Fun Descent: res square
-- statement:
--   The Fun Descent construction uses the res square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L74-L77

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

theorem GlobalTheory.FunDescent.res_square {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) :
    res U ≫ (π ∣_ U).appTop = π.app U ≫ res (π ⁻¹ᵁ U) := by sorry
