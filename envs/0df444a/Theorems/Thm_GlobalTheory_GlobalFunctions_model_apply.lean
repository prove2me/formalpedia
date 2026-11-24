-- Prove2me | Theorems.Thm_GlobalTheory_GlobalFunctions_model_apply
-- name    : GlobalTheory.GlobalFunctions.model_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:56:18.855331+00:00
-- url     : https://prove2.me/theorems/460de51c-30f1-4225-8461-2136d8e8d846
-- title:
--   Global Functions: model apply
-- statement:
--   The Global Functions construction uses the model apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L39-L53

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

theorem GlobalTheory.GlobalFunctions.model_apply {R₀ R B₀ B C₀ C : Type} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [AddCommGroup B₀] [Module R₀ B₀] [AddCommGroup C₀] [Module R₀ C₀]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (β : R ⊗[R₀] B₀ ≃ₗ[R] B) (δ : R ⊗[R₀] C₀ ≃ₗ[R] C) (u₀ : B₀ →ₗ[R₀] C₀) (u : B →ₗ[R] C)
    (h : ∀ b, u (β (1 ⊗ₜ b)) = δ (1 ⊗ₜ u₀ b)) (y : R ⊗[R₀] B₀) :
    u (β y) = δ (u₀.baseChange R y) := by sorry
