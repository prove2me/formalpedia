-- Prove2me | Theorems.Thm_GlobalTheory_T_cancel_artinian_noetherian_summand
-- name    : GlobalTheory.T.cancel_artinian_noetherian_summand
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:47.030565+00:00
-- url     : https://prove2.me/theorems/662f6654-171c-435f-9b4c-e9553206be5e
-- title:
--   T: cancel artinian noetherian summand
-- statement:
--   The T construction uses the cancel artinian noetherian summand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CancelArtinianNoetherianSummandStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CancelArtinianNoetherianSummandStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummand
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummandStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cancel_artinian_noetherian_summand : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P], Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by sorry
