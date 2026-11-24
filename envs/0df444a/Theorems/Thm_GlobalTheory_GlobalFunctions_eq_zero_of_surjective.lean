-- Prove2me | Theorems.Thm_GlobalTheory_GlobalFunctions_eq_zero_of_surjective
-- name    : GlobalTheory.GlobalFunctions.eq_zero_of_surjective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:55:21.518412+00:00
-- url     : https://prove2.me/theorems/7e4b2d19-dbd0-4f98-ba09-026381b5b0a9
-- title:
--   Global Functions: eq zero of surjective
-- statement:
--   The Global Functions construction uses the eq zero of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L130-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L130-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
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
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {R B C : CommRingCat.{0}} {X : Scheme.{0}}

theorem GlobalTheory.GlobalFunctions.eq_zero_of_surjective {p : X ⟶ Spec R} (hp : Function.Surjective p.appTop)
    (i : Spec B ⟶ X) [EffectiveEpi i] {f g : B ⟶ C}
    (H : IsPullback (Spec.map f) (Spec.map g) i i) {φ : R ⟶ B} (hφ : i ≫ p = Spec.map φ)
    {R' : CommRingCat.{0}} (r : B ⟶ R') (hr : Function.Injective (φ ≫ r)) (x : B)
    (hx : f x = g x) (hrx : r x = 0) : x = 0 := by sorry
