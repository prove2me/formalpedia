-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_incl_tmul
-- name    : GlobalTheory.SmoothDescent.incl_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:42.764994+00:00
-- url     : https://prove2.me/theorems/fa16811b-ba63-44b3-8076-313bec060f62
-- title:
--   Smooth Descent: incl tmul
-- statement:
--   The Smooth Descent construction uses the incl tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L100-L102

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

theorem GlobalTheory.SmoothDescent.incl_tmul (S : Subalgebra A R) (s : S) (c : C₁) :
    incl C₁ S (s ⊗ₜ c) = (s : R) • ((1 : R) ⊗ₜ[A] c) := by sorry
