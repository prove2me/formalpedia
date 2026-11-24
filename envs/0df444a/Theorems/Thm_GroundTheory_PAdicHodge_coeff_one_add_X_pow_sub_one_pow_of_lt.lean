-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_coeff_one_add_X_pow_sub_one_pow_of_lt
-- name    : GroundTheory.PAdicHodge.coeff_one_add_X_pow_sub_one_pow_of_lt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:38:33.31059+00:00
-- url     : https://prove2.me/theorems/95ee2d4e-47b6-4909-9298-6f08fa85eb98
-- title:
--   PAdic Hodge: coeff one add X pow sub one pow of lt
-- statement:
--   The PAdic Hodge construction uses the coeff one add X pow sub one pow of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L15-L18

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

theorem GroundTheory.PAdicHodge.coeff_one_add_X_pow_sub_one_pow_of_lt {R : Type*} [CommRing R] (q : ℕ) {m n : ℕ}
    (h : m < n) : (((1 + Polynomial.X : Polynomial R) ^ q - 1) ^ n).coeff m = 0 := by sorry
