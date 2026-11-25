-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FFNorm_exists_conj_mul_eq
-- name    : GlobalTheory.CompanionTheory.FFNorm.exists_conj_mul_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:58.906801+00:00
-- url     : https://prove2.me/theorems/dfd08a3d-2a3a-4256-9810-477949b889e3
-- title:
--   FFNorm: exists conj mul eq
-- statement:
--   The FFNorm construction uses the exists conj mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsConjMulEq.lean#L5-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsConjMulEq.lean#L5-L45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsConjMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FFNorm

theorem GlobalTheory.CompanionTheory.FFNorm.exists_conj_mul_eq : ∀ (κ : Type) [Field κ] [Finite κ] (τ : κ →+* κ), (∀ x, τ (τ x) = x) →
    (∃ x, τ x ≠ x) → ∀ c : κ, τ c = c → ∃ s : κ, τ s * s = c := by sorry
