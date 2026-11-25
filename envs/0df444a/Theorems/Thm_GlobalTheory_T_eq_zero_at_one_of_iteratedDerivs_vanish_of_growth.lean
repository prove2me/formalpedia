-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_at_one_of_iteratedDerivs_vanish_of_growth
-- name    : GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:08.934971+00:00
-- url     : https://prove2.me/theorems/676ef2eb-fd4a-41f6-9588-37ed989e0dd0
-- title:
--   T: eq zero at one of iterated Derivs vanish of growth
-- statement:
--   The T construction uses the eq zero at one of iterated Derivs vanish of growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroAtOneOfIteratedDerivsVanishOfGrowthStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroAtOneOfIteratedDerivsVanishOfGrowthStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroAtOneOfIteratedDerivsVanishOfGrowth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroAtOneOfIteratedDerivsVanishOfGrowthStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth : ∀ (φ : ℕ → ℝ → ℂ) (a b : ℝ), (∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) → (∀ k, φ k 0 = 0) → (∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) → φ 0 1 = 0 := by sorry
