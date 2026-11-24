-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_spm_torusPt
-- name    : GlobalTheory.TorusNil.spm_torusPt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:05.953303+00:00
-- url     : https://prove2.me/theorems/73cc90e0-be1c-4159-85ff-69ae2ca63282
-- title:
--   Torus Nil: spm torus Pt
-- statement:
--   The Torus Nil construction uses the spm torus Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L287-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L287-L302

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

theorem GlobalTheory.TorusNil.spm_torusPt {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (ψ : C →ₐ[A] D) (χ : Multiplicative X →* C) :
    spm ψ ≫ torusPt A X χ = torusPt A X ((ψ : C →* D).comp χ) := by sorry
