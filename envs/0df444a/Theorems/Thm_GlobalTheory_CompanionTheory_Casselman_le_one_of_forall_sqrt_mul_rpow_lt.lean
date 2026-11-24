-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Casselman_le_one_of_forall_sqrt_mul_rpow_lt
-- name    : GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:31:41.632192+00:00
-- url     : https://prove2.me/theorems/d6c9e159-22ae-4f2a-ac1d-a457243bf3c6
-- title:
--   Casselman: le one of forall sqrt mul rpow lt
-- statement:
--   The Casselman construction uses the le one of forall sqrt mul rpow lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeOneOfPowerBounds.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeOneOfPowerBounds.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeOneOfPowerBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Casselman

theorem GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt :
    ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r →
      (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by sorry
