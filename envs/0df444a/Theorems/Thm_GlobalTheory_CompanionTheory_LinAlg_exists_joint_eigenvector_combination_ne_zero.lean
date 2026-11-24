-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LinAlg_exists_joint_eigenvector_combination_ne_zero
-- name    : GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:05.010331+00:00
-- url     : https://prove2.me/theorems/b07d774b-3f76-4545-aa0c-e7d46a8f0c7c
-- title:
--   Lin Alg: exists joint eigenvector combination ne zero
-- statement:
--   The Lin Alg construction uses the exists joint eigenvector combination ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsJointEigenvectorNonzero.lean#L85-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsJointEigenvectorNonzero.lean#L85-L109

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsJointEigenvectorNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LinAlg
open Module

theorem GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero :
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι J : Type) [Fintype J]
      (H : ι → Module.End ℂ W), (∀ i i', Commute (H i) (H i')) →
      ∀ (c : J → ℂ) (s : J → ι) (v : W) (m : ℕ), Module.finrank ℂ W ≤ m →
        ((∑ j, c j • H (s j)) ^ m) v ≠ 0 →
        ∃ v₀ : W, v₀ ≠ 0 ∧ ∃ χ : ι → ℂ, (∀ i, H i v₀ = χ i • v₀) ∧ ∑ j, c j * χ (s j) ≠ 0 := by sorry
