-- Prove2me | Theorems.Thm_GlobalTheory_T_lt_one_of_power_bound
-- name    : GlobalTheory.T.lt_one_of_power_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:10.936113+00:00
-- url     : https://prove2.me/theorems/0e518445-24a5-4ca1-a6ab-a294754e838e
-- title:
--   T: lt one of power bound
-- statement:
--   The T construction uses the lt one of power bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LtOneOfPowerBoundStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LtOneOfPowerBoundStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LtOneOfPowerBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LtOneOfPowerBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lt_one_of_power_bound : ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by sorry
