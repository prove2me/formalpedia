-- Prove2me | Theorems.Thm_GlobalTheory_FunDescent_exists_hom
-- name    : GlobalTheory.FunDescent.exists_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:20.586159+00:00
-- url     : https://prove2.me/theorems/9644480d-7554-4ba1-9437-9f1080193d02
-- title:
--   Fun Descent: exists hom
-- statement:
--   The Fun Descent construction uses the exists hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InvariantFunctionsDescend.lean#L23-L30

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

theorem GlobalTheory.FunDescent.exists_hom {Z : Scheme.{0}} (f : Γ(Z, ⊤)) :
    ∃ g : Z ⟶ Spec (CommRingCat.of (Polynomial ℤ)), g.appTop.hom coord = f := by sorry
