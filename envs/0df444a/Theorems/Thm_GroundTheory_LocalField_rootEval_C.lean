-- Prove2me | Theorems.Thm_GroundTheory_LocalField_rootEval_C
-- name    : GroundTheory.LocalField.rootEval_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:24.03955+00:00
-- url     : https://prove2.me/theorems/866abfc7-9855-418b-9a7d-811357694116
-- title:
--   Local Field: root Eval C
-- statement:
--   The Local Field construction uses the root Eval C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L58-L59

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)

theorem GroundTheory.LocalField.rootEval_C (b : B) : rootEval hP (C b) = AdjoinRoot.of P b := by sorry
