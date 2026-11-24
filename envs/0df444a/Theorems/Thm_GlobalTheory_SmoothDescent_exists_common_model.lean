-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_exists_common_model
-- name    : GlobalTheory.SmoothDescent.exists_common_model
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:16:08.011963+00:00
-- url     : https://prove2.me/theorems/418a3a48-4a02-4e95-937f-c3594ee6dab4
-- title:
--   Smooth Descent: exists common model
-- statement:
--   The Smooth Descent construction uses the exists common model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L12-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothDescent
open TensorProduct

theorem GlobalTheory.SmoothDescent.exists_common_model (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] :
    ∃ (A B₁ C₁ : Type) (_ : CommRing A) (_ : Algebra A R) (_ : CommRing B₁) (_ : CommRing C₁)
      (_ : Algebra A B₁) (_ : Algebra A C₁), IsNoetherianRing A ∧ Algebra.Smooth A B₁ ∧
      Algebra.Smooth A C₁ ∧ Nonempty (R ⊗[A] B₁ ≃ₐ[R] B) ∧ Nonempty (R ⊗[A] C₁ ≃ₐ[R] C) := by sorry
