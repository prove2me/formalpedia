-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_exists_chart
-- name    : GlobalTheory.TorusNil.exists_chart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:47.293364+00:00
-- url     : https://prove2.me/theorems/93601b3e-0d63-4a03-9b3e-98703b9002d1
-- title:
--   Torus Nil: exists chart
-- statement:
--   The Torus Nil construction uses the exists chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L369-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L369-L390

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

theorem GlobalTheory.TorusNil.exists_chart [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R) (j : sp A R ⟶ B) (_ : IsOpenImmersion j.left)
      (ε : R →ₐ[A] A), spm ε ≫ j = 1 := by sorry
