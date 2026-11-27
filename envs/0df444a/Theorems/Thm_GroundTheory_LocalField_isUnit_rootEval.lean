-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isUnit_rootEval
-- name    : GroundTheory.LocalField.isUnit_rootEval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:56.738974+00:00
-- url     : https://prove2.me/theorems/aa87f89e-a8ea-56c5-a6eb-a4d911b636c3
-- title:
--   Local Field: is Unit root Eval
-- statement:
--   The Local Field construction uses the is Unit root Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L85-L87

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

theorem GroundTheory.LocalField.isUnit_rootEval {G : B⟦X⟧} (hG : IsUnit (constantCoeff G)) :
    IsUnit (rootEval hP G) := by sorry
