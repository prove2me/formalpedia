-- Prove2me | Theorems.Thm_GlobalTheory_splitTorus_hom_proper_trivial_local
-- name    : GlobalTheory.splitTorus_hom_proper_trivial_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:16.41041+00:00
-- url     : https://prove2.me/theorems/81969a34-16ba-4e55-b018-a5e2cd5bb6a2
-- title:
--   Global Theory: split Torus hom proper trivial local
-- statement:
--   The Global Theory construction uses the split Torus hom proper trivial local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialLocal.lean#L81-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialLocal.lean#L81-L120

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
open TorusNil TorusLocal

theorem GlobalTheory.splitTorus_hom_proper_trivial_local (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsProper B.hom]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by sorry
