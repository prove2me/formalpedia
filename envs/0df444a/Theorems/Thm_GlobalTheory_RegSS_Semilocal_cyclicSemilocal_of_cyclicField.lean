-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_Semilocal_cyclicSemilocal_of_cyclicField
-- name    : GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:53:33.454823+00:00
-- url     : https://prove2.me/theorems/1d3a6754-f695-48aa-afcf-033bdf9ea751
-- title:
--   Semilocal: cyclic Semilocal of cyclic Field
-- statement:
--   The Semilocal construction uses the cyclic Semilocal of cyclic Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorSemilocalOfCyclicVectorField.lean#L21-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorSemilocalOfCyclicVectorField.lean#L21-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorSemilocalOfCyclicVectorField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS Matrix
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.Semilocal
open Matrix

theorem GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField :
    _root_.GlobalTheory.RegSS.CyclicField → _root_.GlobalTheory.RegSS.CyclicSemilocal := by sorry
