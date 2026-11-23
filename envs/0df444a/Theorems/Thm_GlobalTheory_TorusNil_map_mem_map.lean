-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_map_mem_map
-- name    : GlobalTheory.TorusNil.map_mem_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:01.507508+00:00
-- url     : https://prove2.me/theorems/54ba50b6-a73a-409d-9b98-93956b10f34e
-- title:
--   Torus Nil: map mem map
-- statement:
--   The Torus Nil construction uses the map mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L401-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L401-L410

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

theorem GlobalTheory.TorusNil.map_mem_map {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (I : Ideal A) (r : C →ₗ[A] D) {x : C} (hx : x ∈ I.map (algebraMap A C)) :
    r x ∈ I.map (algebraMap A D) := by sorry
