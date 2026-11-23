-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreInjective_injective_baseChange
-- name    : GlobalTheory.FlatFibreInjective.injective_baseChange
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:02.500764+00:00
-- url     : https://prove2.me/theorems/4cf0ceb4-69e3-4329-b7d7-8720da4ba7bc
-- title:
--   Flat Fibre Injective: injective base Change
-- statement:
--   The Flat Fibre Injective construction uses the injective base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L102-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L102-L158

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
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
open GlobalTheory GlobalTheory.FlatFibreInjective
open TensorProduct

theorem GlobalTheory.FlatFibreInjective.injective_baseChange :
    ∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R]
      [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀]
      [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁),
      (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k],
        Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R) := by sorry
