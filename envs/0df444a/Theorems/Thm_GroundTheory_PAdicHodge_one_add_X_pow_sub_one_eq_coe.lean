-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_one_add_X_pow_sub_one_eq_coe
-- name    : GroundTheory.PAdicHodge.one_add_X_pow_sub_one_eq_coe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:19.0408+00:00
-- url     : https://prove2.me/theorems/91c059b7-983b-4832-b14a-024503d9c88b
-- title:
--   PAdic Hodge: one add X pow sub one eq coe
-- statement:
--   The PAdic Hodge construction uses the one add X pow sub one eq coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L70-L73

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries

theorem GroundTheory.PAdicHodge.one_add_X_pow_sub_one_eq_coe (q : ℕ) :
    ((1 + X : ℚ⟦X⟧) ^ q - 1) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1 : Polynomial ℚ) : ℚ⟦X⟧) := by sorry
