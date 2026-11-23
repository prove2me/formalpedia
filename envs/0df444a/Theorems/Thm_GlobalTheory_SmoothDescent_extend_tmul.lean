-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_extend_tmul
-- name    : GlobalTheory.SmoothDescent.extend_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:39.927899+00:00
-- url     : https://prove2.me/theorems/90193475-c34a-4df6-8aa8-d987b4cfd037
-- title:
--   Smooth Descent: extend tmul
-- statement:
--   The Smooth Descent construction uses the extend tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L115-L118

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

theorem GlobalTheory.SmoothDescent.extend_tmul (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) (s : S) (b : B₁) :
    extend S ψ (s ⊗ₜ b) = s • ψ b := by sorry
