-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExtTensorFixed_mem_range_lTensor_fixed
-- name    : GlobalTheory.CompanionTheory.ExtTensorFixed.mem_range_lTensor_fixed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:46.160481+00:00
-- url     : https://prove2.me/theorems/4e6b06ea-46ba-4070-893d-674cf3b84205
-- title:
--   Ext Tensor Fixed: mem range l Tensor fixed
-- statement:
--   The Ext Tensor Fixed construction uses the mem range l Tensor fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalFixedTensor.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDimensionalFixedTensor.lean#L28-L43

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

theorem GlobalTheory.CompanionTheory.ExtTensorFixed.mem_range_lTensor_fixed (σ : Representation ℂ G W) (K : Subgroup G) (y : X ⊗[ℂ] W)
    (hy : ∀ k : K, (σ (k : G)).lTensor X y = y) :
    y ∈ LinearMap.range ((fixed σ K).subtype.lTensor X) := by sorry
