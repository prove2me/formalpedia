-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PiTensor_map_injective_of_injective
-- name    : GlobalTheory.CompanionTheory.PiTensor.map_injective_of_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:35.549797+00:00
-- url     : https://prove2.me/theorems/ee3f17ac-a65c-5fb5-a4ee-2253a5160c55
-- title:
--   Pi Tensor: map injective of injective
-- statement:
--   The Pi Tensor construction uses the map injective of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapInjectiveOfInjective.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapInjectiveOfInjective.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapInjectiveOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PiTensor

theorem GlobalTheory.CompanionTheory.PiTensor.map_injective_of_injective
    (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
    (f : ∀ i, M i →ₗ[K] N i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by sorry
