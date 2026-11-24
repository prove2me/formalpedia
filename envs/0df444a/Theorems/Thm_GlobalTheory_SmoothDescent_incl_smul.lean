-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_incl_smul
-- name    : GlobalTheory.SmoothDescent.incl_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:11.502633+00:00
-- url     : https://prove2.me/theorems/3f388af0-80ae-4913-8538-19dd66aa1901
-- title:
--   Smooth Descent: incl smul
-- statement:
--   The Smooth Descent construction uses the incl smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L104-L109

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

theorem GlobalTheory.SmoothDescent.incl_smul (S : Subalgebra A R) (s : S) (x : S ⊗[A] C₁) :
    incl C₁ S (s • x) = (s : R) • incl C₁ S x := by sorry
