-- Prove2me | Theorems.Thm_GlobalTheory_isAdicComplete_of_pow_le_of_le
-- name    : GlobalTheory.isAdicComplete_of_pow_le_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:17.154949+00:00
-- url     : https://prove2.me/theorems/cf0e08f7-fc1f-4c7e-9ee5-1d58d05f8d7f
-- title:
--   Global Theory: is Adic Complete of pow le of le
-- statement:
--   The Global Theory construction uses the is Adic Complete of pow le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsAdicCompleteOfFgOfNatCastMem.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsAdicCompleteOfFgOfNatCastMem.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.isAdicComplete_of_pow_le_of_le {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {I J : Ideal R} (hI : IsAdicComplete I M) {n : ℕ} (hJI : J ^ n ≤ I)
    (hIJ : I ≤ J) : IsAdicComplete J M := by sorry
