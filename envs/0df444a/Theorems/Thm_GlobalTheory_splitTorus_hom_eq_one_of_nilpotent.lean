-- Prove2me | Theorems.Thm_GlobalTheory_splitTorus_hom_eq_one_of_nilpotent
-- name    : GlobalTheory.splitTorus_hom_eq_one_of_nilpotent
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:17.017623+00:00
-- url     : https://prove2.me/theorems/67a9d8c9-24a4-4748-a2b0-8d9a4b5bff24
-- title:
--   Global Theory: split Torus hom eq one of nilpotent
-- statement:
--   The Global Theory construction uses the split Torus hom eq one of nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L416-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L416-L477

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
open TorusNil

theorem GlobalTheory.splitTorus_hom_eq_one_of_nilpotent (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A)
    (hJ : IsNilpotent J) (X : Type) [AddCommGroup X] (B : Over (Spec (CommRingCat.of A)))
    [GrpObj B] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f)
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map
        (toUnit _ ≫ η[B])) : f = toUnit _ ≫ η[B] := by sorry
