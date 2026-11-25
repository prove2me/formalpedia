-- Prove2me | Theorems.Thm_GlobalTheory_T_isRat_of_hankel_eventually_eq_zero
-- name    : GlobalTheory.T.isRat_of_hankel_eventually_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:30.310393+00:00
-- url     : https://prove2.me/theorems/abad89b2-20c8-470e-86c4-7ce751811cba
-- title:
--   T: is Rat of hankel eventually eq zero
-- statement:
--   The T construction uses the is Rat of hankel eventually eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZeroStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZeroStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isRat_of_hankel_eventually_eq_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ), (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by sorry
