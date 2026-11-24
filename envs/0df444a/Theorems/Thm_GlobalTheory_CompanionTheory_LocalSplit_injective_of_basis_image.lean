-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalSplit_injective_of_basis_image
-- name    : GlobalTheory.CompanionTheory.LocalSplit.injective_of_basis_image
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:49.814795+00:00
-- url     : https://prove2.me/theorems/14c1dab8-80a6-4d7f-a555-fc7115ae9f85
-- title:
--   Local Split: injective of basis image
-- statement:
--   The Local Split construction uses the injective of basis image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFreeKernelSplitting.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFreeKernelSplitting.lean#L6-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalSplit

theorem GlobalTheory.CompanionTheory.LocalSplit.injective_of_basis_image {k V U ι : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U] (b : Module.Basis ι k V) (g : V →ₗ[k] U)
    (h : LinearIndependent k (g ∘ b)) : Function.Injective g := by sorry
