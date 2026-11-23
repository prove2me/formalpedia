-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_torusPt_fst
-- name    : GlobalTheory.TorusNil.torusPt_fst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:06.275692+00:00
-- url     : https://prove2.me/theorems/dd566de7-4553-4927-87a1-c313ccf70bc2
-- title:
--   Torus Nil: torus Pt fst
-- statement:
--   The Torus Nil construction uses the torus Pt fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L263-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L263-L272

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

theorem GlobalTheory.TorusNil.torusPt_fst {C : Type} [CommRing C] [Algebra A C] (χ : Multiplicative X →* C) :
    ∃ φ : AddMonoidAlgebra (ULift.{0} ℤ) X →+* C,
      (∀ x, φ (AddMonoidAlgebra.single x 1) = χ (Multiplicative.ofAdd x)) ∧
      (torusPt A X χ).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ _) =
        Spec.map (CommRingCat.ofHom φ) := by sorry
