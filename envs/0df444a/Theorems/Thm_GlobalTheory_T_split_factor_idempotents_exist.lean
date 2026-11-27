-- Prove2me | Theorems.Thm_GlobalTheory_T_split_factor_idempotents_exist
-- name    : GlobalTheory.T.split_factor_idempotents_exist
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-27T06:24:13.005865+00:00
-- url     : https://prove2.me/theorems/6832907b-c477-4b5a-8e77-cfe618f221e1
-- title:
--   T: split factor idempotents exist
-- statement:
--   The T construction uses the split factor idempotents exist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitFactorIdempotentsExistStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitFactorIdempotentsExistStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitFactorIdempotentsExist
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitFactorIdempotentsExistStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.split_factor_idempotents_exist : GlobalTheory.RegSS.SplitIdempotents := by sorry
