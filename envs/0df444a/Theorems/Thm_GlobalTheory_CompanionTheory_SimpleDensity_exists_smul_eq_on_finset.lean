-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SimpleDensity_exists_smul_eq_on_finset
-- name    : GlobalTheory.CompanionTheory.SimpleDensity.exists_smul_eq_on_finset
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:04.588263+00:00
-- url     : https://prove2.me/theorems/5feaa63b-6109-4192-b4fc-a5ef891a35ce
-- title:
--   Simple Density: exists smul eq on finset
-- statement:
--   The Simple Density construction uses the exists smul eq on finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmulEqOnFinset.lean#L5-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmulEqOnFinset.lean#L5-L32

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

theorem GlobalTheory.CompanionTheory.SimpleDensity.exists_smul_eq_on_finset {R ι : Type} [Ring R] [Fintype ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (hne : ∀ i j, i ≠ j → ∀ φ : M i →ₗ[R] M j, φ = 0)
    (f : ∀ i, M i →+ M i)
    (hf : ∀ i (φ : M i →ₗ[R] M i) x, f i (φ x) = φ (f i x))
    (s : Finset (∀ i, M i)) :
    ∃ r : R, ∀ m ∈ s, ∀ i, f i (m i) = r • m i := by sorry
