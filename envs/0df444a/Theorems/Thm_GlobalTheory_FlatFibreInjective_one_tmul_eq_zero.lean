-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreInjective_one_tmul_eq_zero
-- name    : GlobalTheory.FlatFibreInjective.one_tmul_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:45.034222+00:00
-- url     : https://prove2.me/theorems/77227d49-a867-4219-b3f4-751258a04b5b
-- title:
--   Flat Fibre Injective: one tmul eq zero
-- statement:
--   The Flat Fibre Injective construction uses the one tmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L57-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L57-L75

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

theorem GlobalTheory.FlatFibreInjective.one_tmul_eq_zero {R₀ M C₀ C₁ k : Type} [CommRing R₀] [AddCommGroup M] [Module R₀ M]
    [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁]
    [Field k] [Algebra R₀ k] (φ : C₀ →ₗ[R₀] C₁) (hφ : Function.Injective (φ.baseChange k))
    (y : M ⊗[R₀] C₀) (hy : φ.lTensor M y = 0) : (1 : k) ⊗ₜ[R₀] y = 0 := by sorry
