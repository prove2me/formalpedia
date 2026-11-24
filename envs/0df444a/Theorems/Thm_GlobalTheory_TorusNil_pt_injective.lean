-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_pt_injective
-- name    : GlobalTheory.TorusNil.pt_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:48.090936+00:00
-- url     : https://prove2.me/theorems/b020e550-7f3c-4113-b009-6aacd98cc30a
-- title:
--   Torus Nil: pt injective
-- statement:
--   The Torus Nil construction uses the pt injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L122-L126

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
omit [GrpObj B]

theorem GlobalTheory.TorusNil.pt_injective {C : Type} [CommRing C] [Algebra A C] {φ ψ : R →ₐ[A] C}
    (h : spm φ ≫ j = spm ψ ≫ j) : φ = ψ := by sorry
