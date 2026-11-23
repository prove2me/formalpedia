-- Prove2me | Theorems.Thm_GlobalTheory_FunDescent_res_comp_appTop
-- name    : GlobalTheory.FunDescent.res_comp_appTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:16.703272+00:00
-- url     : https://prove2.me/theorems/bd632b6b-8f43-4723-97b5-67befec69c91
-- title:
--   Fun Descent: res comp app Top
-- statement:
--   The Fun Descent construction uses the res comp app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L67-L72

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

theorem GlobalTheory.FunDescent.res_comp_appTop {X Z : Scheme.{0}} (U : X.Opens) (g : Z ⟶ U.toScheme) (k : Z ⟶ X)
    (e : k = g ≫ U.ι) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    res U ≫ g.appTop = k.appLE U ⊤ h := by sorry
