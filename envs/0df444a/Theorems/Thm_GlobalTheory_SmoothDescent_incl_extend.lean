-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_incl_extend
-- name    : GlobalTheory.SmoothDescent.incl_extend
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:14:56.851462+00:00
-- url     : https://prove2.me/theorems/e3ab15cb-78a8-4289-846d-4e515672f60e
-- title:
--   Smooth Descent: incl extend
-- statement:
--   The Smooth Descent construction uses the incl extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L120-L126

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
variable {A R B₁ C₁ : Type} [CommRing A] [CommRing R] [CommRing B₁] [CommRing C₁] [Algebra A R]
  [Algebra A B₁] [Algebra A C₁]

theorem GlobalTheory.SmoothDescent.incl_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁)
    (ψ : B₁ →ₐ[A] S ⊗[A] C₁) (h : ∀ b, incl C₁ S (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    incl C₁ S (extend S ψ x) = F (incl B₁ S x) := by sorry
