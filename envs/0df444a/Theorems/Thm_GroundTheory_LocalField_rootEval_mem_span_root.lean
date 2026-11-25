-- Prove2me | Theorems.Thm_GroundTheory_LocalField_rootEval_mem_span_root
-- name    : GroundTheory.LocalField.rootEval_mem_span_root
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:51.231429+00:00
-- url     : https://prove2.me/theorems/9fb7bd35-0e7a-4d94-93f2-8257f441b725
-- title:
--   Local Field: root Eval mem span root
-- statement:
--   The Local Field construction uses the root Eval mem span root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L79-L83

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

theorem GroundTheory.LocalField.rootEval_mem_span_root {G : B⟦X⟧} (hG : constantCoeff G = 0) :
    rootEval hP G ∈ Ideal.span {AdjoinRoot.root P} := by sorry
