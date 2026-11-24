-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_pt_one
-- name    : GlobalTheory.TorusNil.pt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:29.739392+00:00
-- url     : https://prove2.me/theorems/401066c8-e867-4acc-b1b9-9b19254baff3
-- title:
--   Torus Nil: pt one
-- statement:
--   The Torus Nil construction uses the pt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L130-L132

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
omit [IsOpenImmersion j.left]
include hε

theorem GlobalTheory.TorusNil.pt_one (C : Type) [CommRing C] [Algebra A C] :
    spm ((Algebra.ofId A C).comp ε) ≫ j = 1 := by sorry
