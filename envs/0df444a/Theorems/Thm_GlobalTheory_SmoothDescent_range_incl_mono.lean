-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDescent_range_incl_mono
-- name    : GlobalTheory.SmoothDescent.range_incl_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:04.540289+00:00
-- url     : https://prove2.me/theorems/11ce7533-6edf-49f2-9140-897a85e11f80
-- title:
--   Smooth Descent: range incl mono
-- statement:
--   The Smooth Descent construction uses the range incl mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsNoetherianModelOfSmooth.lean#L37-L43

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

theorem GlobalTheory.SmoothDescent.range_incl_mono {S T : Subalgebra A R} (h : S ≤ T) :
    (incl C₁ S).range ≤ (incl C₁ T).range := by sorry
