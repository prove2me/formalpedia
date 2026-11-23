-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_pullback_map_fst
-- name    : GlobalTheory.TorusNil.pullback_map_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:07.149688+00:00
-- url     : https://prove2.me/theorems/46d418a9-de8e-402c-9f03-3655925ed446
-- title:
--   Torus Nil: pullback map fst
-- statement:
--   The Torus Nil construction uses the pullback map fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L215-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L215-L221

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

theorem GlobalTheory.TorusNil.pullback_map_fst {S S' : Scheme.{0}} {p : S' ⟶ S} {Z : Over S'} {V W : Over S}
    (u : Z ⟶ (Over.pullback p).obj V) (f : V ⟶ W) :
    (u ≫ (Over.pullback p).map f).left ≫ pullback.fst W.hom p =
      u.left ≫ pullback.fst V.hom p ≫ f.left := by sorry
