-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_torus_diag
-- name    : GlobalTheory.TorusNil.torus_diag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:36.739924+00:00
-- url     : https://prove2.me/theorems/092a2019-70c4-4249-a7d9-9c248fd92874
-- title:
--   Torus Nil: torus diag
-- statement:
--   The Torus Nil construction uses the torus diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L334-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L334-L342

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

theorem GlobalTheory.TorusNil.torus_diag :
    (spm (dm A X (AddMonoidHom.inl X X)) ≫ torusPt A X (AddMonoidAlgebra.of A X)) *
      (spm (dm A X (AddMonoidHom.inr X X)) ≫ torusPt A X (AddMonoidAlgebra.of A X)) =
    spm (dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X))) ≫
      torusPt A X (AddMonoidAlgebra.of A X) := by sorry
