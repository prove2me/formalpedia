-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalSplit_ker_facts
-- name    : GlobalTheory.CompanionTheory.LocalSplit.ker_facts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:52:01.358156+00:00
-- url     : https://prove2.me/theorems/43ecbc13-7746-4d5a-a4d2-cd5aa971c02c
-- title:
--   Local Split: ker facts
-- statement:
--   The Local Split construction uses the ker facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFreeKernelSplitting.lean#L16-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFreeKernelSplitting.lean#L16-L45

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

theorem GlobalTheory.CompanionTheory.LocalSplit.ker_facts {A Q : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Free A Q] (s : ℕ)
    (f : (Fin s → A) →ₗ[A] Q) (p : Q →ₗ[A] (Fin s → A)) (h : p ∘ₗ f = LinearMap.id) :
    Module.Free A (LinearMap.ker p) ∧ Module.Finite A (LinearMap.ker p) ∧
      s + Module.finrank A (LinearMap.ker p) = Module.finrank A Q := by sorry
