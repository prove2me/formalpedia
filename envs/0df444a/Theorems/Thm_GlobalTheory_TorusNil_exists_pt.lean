-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_exists_pt
-- name    : GlobalTheory.TorusNil.exists_pt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:51.00084+00:00
-- url     : https://prove2.me/theorems/cd117280-99c4-4160-9963-e9e4e16a72d4
-- title:
--   Torus Nil: exists pt
-- statement:
--   The Torus Nil construction uses the exists pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L136-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L136-L151

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
variable {B : Over (Spec (CommRingCat.of A))} [GrpObj B] {R : Type} [CommRing R] [Algebra A R]
  (j : sp A R ⟶ B) [IsOpenImmersion j.left] (ε : R →ₐ[A] A) (hε : spm ε ≫ j = 1)
include hε

theorem GlobalTheory.TorusNil.exists_pt {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (π : C →ₐ[A] D) (hs : Function.Surjective π) (hn : ∀ x, π x = 0 → IsNilpotent x)
    (g : sp A C ⟶ B) (hg : spm π ≫ g = 1) : ∃ φ : R →ₐ[A] C, spm φ ≫ j = g := by sorry
