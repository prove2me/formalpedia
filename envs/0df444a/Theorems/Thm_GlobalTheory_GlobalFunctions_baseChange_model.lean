-- Prove2me | Theorems.Thm_GlobalTheory_GlobalFunctions_baseChange_model
-- name    : GlobalTheory.GlobalFunctions.baseChange_model
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:55:19.120782+00:00
-- url     : https://prove2.me/theorems/2224a6a0-2382-4c24-a4c1-96026f836948
-- title:
--   Global Functions: base Change model
-- statement:
--   The Global Functions construction uses the base Change model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L24-L37

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

theorem GlobalTheory.GlobalFunctions.baseChange_model {R₀ R k B₀ B C₀ C : Type} [CommRing R₀] [CommRing R] [CommRing k]
    [Algebra R₀ R] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k]
    [AddCommGroup B₀] [Module R₀ B₀] [AddCommGroup C₀] [Module R₀ C₀]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (β : R ⊗[R₀] B₀ ≃ₗ[R] B) (δ : R ⊗[R₀] C₀ ≃ₗ[R] C) (u₀ : B₀ →ₗ[R₀] C₀) (u : B →ₗ[R] C)
    (h : ∀ b, u (β (1 ⊗ₜ b)) = δ (1 ⊗ₜ u₀ b)) (y : k ⊗[R₀] B₀) :
    u.baseChange k (β.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y)) =
    δ.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k C₀).symm (u₀.baseChange k y)) := by sorry
