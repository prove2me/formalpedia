-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_cyclicField
-- name    : GlobalTheory.RegSS.cyclicField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:14.947398+00:00
-- url     : https://prove2.me/theorems/5552c7e7-e01d-4d15-a02e-de365d22f712
-- title:
--   Reg SS: cyclic Field
-- statement:
--   The Reg SS construction uses the cyclic Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorOfSeparableCharpolyField.lean#L89-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorOfSeparableCharpolyField.lean#L89-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorOfSeparableCharpolyField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.RegSS

theorem GlobalTheory.RegSS.cyclicField : GlobalTheory.RegSS.CyclicField := by sorry
