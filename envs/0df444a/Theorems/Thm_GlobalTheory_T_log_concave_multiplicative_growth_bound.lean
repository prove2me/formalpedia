-- Prove2me | Theorems.Thm_GlobalTheory_T_log_concave_multiplicative_growth_bound
-- name    : GlobalTheory.T.log_concave_multiplicative_growth_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:12.834938+00:00
-- url     : https://prove2.me/theorems/a348b1fd-a2e7-512d-993c-20bf3fc1c7a7
-- title:
--   T: log concave multiplicative growth bound
-- statement:
--   The T construction uses the log concave multiplicative growth bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogConcaveMultiplicativeGrowthBoundStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogConcaveMultiplicativeGrowthBoundStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogConcaveMultiplicativeGrowthBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogConcaveMultiplicativeGrowthBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.log_concave_multiplicative_growth_bound : ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by sorry
