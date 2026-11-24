-- Prove2me | Theorems.Thm_GlobalTheory_T_le_one_of_power_bounds
-- name    : GlobalTheory.T.le_one_of_power_bounds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:51:12.089493+00:00
-- url     : https://prove2.me/theorems/953b0c8d-1338-4839-8d98-9d9f3d593a89
-- title:
--   T: le one of power bounds
-- statement:
--   The T construction uses the le one of power bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeOneOfPowerBoundsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeOneOfPowerBoundsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeOneOfPowerBounds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeOneOfPowerBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.le_one_of_power_bounds : ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r → (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by sorry
