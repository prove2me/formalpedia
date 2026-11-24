-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Casselman_lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one
-- name    : GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:31:25.830246+00:00
-- url     : https://prove2.me/theorems/69b0f94c-a286-4b28-bd44-36a4b1c2e6b4
-- title:
--   Casselman: lt one of inv mul sqrt mul rpow two lt one
-- statement:
--   The Casselman construction uses the lt one of inv mul sqrt mul rpow two lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LtOneOfPowerBound.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LtOneOfPowerBound.lean#L5-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LtOneOfPowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Casselman

theorem GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one :
    ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by sorry
