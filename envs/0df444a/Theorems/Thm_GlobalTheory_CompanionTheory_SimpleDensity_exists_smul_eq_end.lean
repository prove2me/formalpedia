-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SimpleDensity_exists_smul_eq_end
-- name    : GlobalTheory.CompanionTheory.SimpleDensity.exists_smul_eq_end
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:02:23.178136+00:00
-- url     : https://prove2.me/theorems/744a3e6f-e1c2-401e-bc82-1d5b8c5b4639
-- title:
--   Simple Density: exists smul eq end
-- statement:
--   The Simple Density construction uses the exists smul eq end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmulEqOnFinset.lean#L51-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmulEqOnFinset.lean#L51-L79

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SimpleDensity

theorem GlobalTheory.CompanionTheory.SimpleDensity.exists_smul_eq_end : ∀ (A : Type) [Ring A] [Algebra ℂ A] (J : Type) [Fintype J] (M : J → Type)
    [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] [∀ j, Module A (M j)] [∀ j, IsScalarTower ℂ A (M j)]
    [∀ j, FiniteDimensional ℂ (M j)] [∀ j, IsSimpleModule A (M j)],
    (∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) →
      ∀ f : ∀ j, Module.End ℂ (M j), ∃ a : A, ∀ j (x : M j), a • x = f j x := by sorry
