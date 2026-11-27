-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_splitIdempotents
-- name    : GlobalTheory.RegSS.splitIdempotents
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T06:22:04.885798+00:00
-- url     : https://prove2.me/theorems/8718b167-0cc5-5b64-941e-b8d4b20c904d
-- title:
--   Reg SS: split Idempotents
-- statement:
--   The Reg SS construction uses the split Idempotents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitFactorIdempotentsExist.lean#L45-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitFactorIdempotentsExist.lean#L45-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitFactorIdempotentsExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS

theorem GlobalTheory.RegSS.splitIdempotents : SplitIdempotents := by sorry
