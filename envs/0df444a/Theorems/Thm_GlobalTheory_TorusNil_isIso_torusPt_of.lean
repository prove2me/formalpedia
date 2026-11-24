-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_isIso_torusPt_of
-- name    : GlobalTheory.TorusNil.isIso_torusPt_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:44.145053+00:00
-- url     : https://prove2.me/theorems/104347e6-cb15-4cc3-a71c-42ec84e7fb7d
-- title:
--   Torus Nil: is Iso torus Pt of
-- statement:
--   The Torus Nil construction uses the is Iso torus Pt of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L305-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L305-L329

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
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
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable (A) (X : Type) [AddCommGroup X]
open scoped AlgebraMonoidAlgebra

theorem GlobalTheory.TorusNil.isIso_torusPt_of :
    IsIso (torusPt A X (AddMonoidAlgebra.of A X)).left := by sorry
