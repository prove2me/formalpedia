-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalSplit_exists_section
-- name    : GlobalTheory.CompanionTheory.LocalSplit.exists_section
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:48.138595+00:00
-- url     : https://prove2.me/theorems/884ba70c-a8fa-48ec-8c04-cac28f9a11ab
-- title:
--   Local Split: exists section
-- statement:
--   The Local Split construction uses the exists section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFreeKernelSplitting.lean#L47-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFreeKernelSplitting.lean#L47-L92

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

theorem GlobalTheory.CompanionTheory.LocalSplit.exists_section {A Q P : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup P] [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P]
    [Module.Free A P] (d : Q →ₗ[A] P) :
    ∃ (s : ℕ) (f : (Fin s → A) →ₗ[A] Q) (t : P →ₗ[A] (Fin s → A)),
      t ∘ₗ (d ∘ₗ f) = LinearMap.id ∧
      s + Module.finrank (IsLocalRing.ResidueField A)
        (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) = Module.finrank A Q := by sorry
