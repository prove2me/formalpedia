-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_exists_retraction
-- name    : GlobalTheory.TorusNil.exists_retraction
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:11:58.69114+00:00
-- url     : https://prove2.me/theorems/d00b54c9-af93-4cc8-a0f5-62311ebaa4c3
-- title:
--   Torus Nil: exists retraction
-- statement:
--   The Torus Nil construction uses the exists retraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L344-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L344-L365

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

theorem GlobalTheory.TorusNil.exists_retraction : ∃ r : AddMonoidAlgebra A (X × X) →ₗ[A] AddMonoidAlgebra A X,
    ∀ d, r (dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) d -
      (dm A X (AddMonoidHom.inl X X) d + dm A X (AddMonoidHom.inr X X) d)) = d := by sorry
