-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermitianCommuting_exists_maximal_commuting_hermitian_subspace
-- name    : GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:26.366373+00:00
-- url     : https://prove2.me/theorems/76139d47-d3ed-4002-9909-4cac3f06ed47
-- title:
--   Hermitian Commuting: exists maximal commuting hermitian subspace
-- statement:
--   The Hermitian Commuting construction uses the exists maximal commuting hermitian subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsMaximalAbelianHermitian.lean#L6-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsMaximalAbelianHermitian.lean#L6-L48

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsMaximalAbelianHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermitianCommuting

theorem GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace {n : ℕ}
    (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧
      (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by sorry
