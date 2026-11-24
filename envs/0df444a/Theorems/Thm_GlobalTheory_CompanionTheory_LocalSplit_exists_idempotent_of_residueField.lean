-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalSplit_exists_idempotent_of_residueField
-- name    : GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:49.318719+00:00
-- url     : https://prove2.me/theorems/06105bf1-b510-48f2-a983-f8774ea91722
-- title:
--   Local Split: exists idempotent of residue Field
-- statement:
--   The Local Split construction uses the exists idempotent of residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFreeKernelSplitting.lean#L94-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFreeKernelSplitting.lean#L94-L116

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

theorem GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField (A Q P : Type) [CommRing A] [IsLocalRing A]
    [AddCommGroup Q] [Module A Q] [AddCommGroup P] [Module A P] [Module.Finite A Q]
    [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P) :
    ∃ r : P →ₗ[A] Q, (r ∘ₗ d ∘ₗ r ∘ₗ d = r ∘ₗ d) ∧ Module.Free A (LinearMap.ker (r ∘ₗ d)) ∧
      Module.Finite A (LinearMap.ker (r ∘ₗ d)) ∧
      Module.finrank A (LinearMap.ker (r ∘ₗ d)) =
        Module.finrank (IsLocalRing.ResidueField A)
          (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) := by sorry
