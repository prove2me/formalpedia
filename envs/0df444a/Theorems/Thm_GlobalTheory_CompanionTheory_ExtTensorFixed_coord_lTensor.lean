-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExtTensorFixed_coord_lTensor
-- name    : GlobalTheory.CompanionTheory.ExtTensorFixed.coord_lTensor
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:20.13261+00:00
-- url     : https://prove2.me/theorems/497f099f-cdc2-4675-8278-11eceaf409ef
-- title:
--   Ext Tensor Fixed: coord l Tensor
-- statement:
--   The Ext Tensor Fixed construction uses the coord l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalFixedTensor.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalFixedTensor.lean#L20-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalFixedTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExtTensorFixed
variable {G H V W X ι : Type} [DecidableEq ι] [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

theorem GlobalTheory.CompanionTheory.ExtTensorFixed.coord_lTensor (b : Module.Basis ι ℂ X) (f : W →ₗ[ℂ] W) (y : X ⊗[ℂ] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (f.lTensor X y) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b y i) := by sorry
