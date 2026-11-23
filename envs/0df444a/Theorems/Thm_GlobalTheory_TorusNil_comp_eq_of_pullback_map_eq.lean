-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_comp_eq_of_pullback_map_eq
-- name    : GlobalTheory.TorusNil.comp_eq_of_pullback_map_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:48.157525+00:00
-- url     : https://prove2.me/theorems/f0457998-7a50-44be-b071-788930c8d7f0
-- title:
--   Torus Nil: comp eq of pullback map eq
-- statement:
--   The Torus Nil construction uses the comp eq of pullback map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L223-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L223-L234

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

theorem GlobalTheory.TorusNil.comp_eq_of_pullback_map_eq {S S' : Scheme.{0}} {p : S' ⟶ S} {Z V W : Over S}
    {f g : V ⟶ W} (h : (Over.pullback p).map f = (Over.pullback p).map g) (t : Z ⟶ V)
    (s : Z.left ⟶ S') (hs : s ≫ p = Z.hom) : t ≫ f = t ≫ g := by sorry
