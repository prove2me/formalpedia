-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_isNilpotent_of_mem_map
-- name    : GlobalTheory.TorusNil.isNilpotent_of_mem_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:12.093271+00:00
-- url     : https://prove2.me/theorems/73c91ff2-fc5c-4805-bed6-0c3877f83c5d
-- title:
--   Torus Nil: is Nilpotent of mem map
-- statement:
--   The Torus Nil construction uses the is Nilpotent of mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L392-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L392-L399

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

theorem GlobalTheory.TorusNil.isNilpotent_of_mem_map {C : Type} [CommRing C] [Algebra A C] {J : Ideal A}
    (hJ : IsNilpotent J) (k : ℕ) (x : C) (hx : x ∈ (J ^ (k + 1)).map (algebraMap A C)) :
    IsNilpotent x := by sorry
