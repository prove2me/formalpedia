-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_plusTensorBijective
-- name    : GlobalTheory.RegSS.plusTensorBijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:21:47.097386+00:00
-- url     : https://prove2.me/theorems/6ee2b120-c2e2-5128-a4c7-d99589f4f9b8
-- title:
--   Reg SS: plus Tensor Bijective
-- statement:
--   The Reg SS construction uses the plus Tensor Bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleSelfAdjointPartTensorBijective.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleSelfAdjointPartTensorBijective.lean#L60-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleSelfAdjointPartTensorBijective
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

theorem GlobalTheory.RegSS.plusTensorBijective : PlusTensorBijective := by sorry
