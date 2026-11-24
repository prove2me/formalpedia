-- Prove2me | Theorems.Thm_GlobalTheory_T_isField_or_exists_swapped_idempotent_of_quadraticEtale
-- name    : GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:06.720027+00:00
-- url     : https://prove2.me/theorems/4ee1c5dc-0b9e-4934-a8c4-d92dcc1d87e9
-- title:
--   T: is Field or exists swapped idempotent of quadratic Etale
-- statement:
--   The T construction uses the is Field or exists swapped idempotent of quadratic Etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsFieldOrExistsSwappedIdempotentOfQuadraticEtale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by sorry
