-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_splitClosed
-- name    : GlobalTheory.RegSS.splitClosed
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:22:13.962648+00:00
-- url     : https://prove2.me/theorems/cb6ffdc8-f55c-4236-a7c7-2fbc3b989f82
-- title:
--   Reg SS: split Closed
-- statement:
--   The Reg SS construction uses the split Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EtaleTensorQuadraticSplitAlgClosed.lean#L74-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EtaleTensorQuadraticSplitAlgClosed.lean#L74-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EtaleTensorQuadraticSplitAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS

theorem GlobalTheory.RegSS.splitClosed : SplitClosed := by sorry
