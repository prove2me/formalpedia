-- Prove2me | Theorems.Thm_GlobalTheory_TorusLocal_pullback_map_eq_one
-- name    : GlobalTheory.TorusLocal.pullback_map_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:12.383309+00:00
-- url     : https://prove2.me/theorems/77487d88-befc-4dff-9f56-58c129d59f68
-- title:
--   Torus Local: pullback map eq one
-- statement:
--   The Torus Local construction uses the pullback map eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialLocal.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialLocal.lean#L16-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
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
open GlobalTheory
open GlobalTheory.TorusLocal

theorem GlobalTheory.TorusLocal.pullback_map_eq_one {S S' : Scheme.{0}} (p : S' ⟶ S) (X : Type) [AddCommGroup X]
    (B : Over S) [GrpObj B] (f : splitTorus S X ⟶ B) (hf : IsMonHom f)
    (h : ∀ g : splitTorus S' X ⟶ (Over.pullback p).obj B, IsMonHom g →
      g = toUnit _ ≫ η[(Over.pullback p).obj B]) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by sorry
