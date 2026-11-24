-- Prove2me | Theorems.Thm_GroundTheory_LocalField_rootEval_eq_zero_iff
-- name    : GroundTheory.LocalField.rootEval_eq_zero_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:48.413721+00:00
-- url     : https://prove2.me/theorems/f5a075c1-b99f-429a-a421-217cabe81705
-- title:
--   Local Field: root Eval eq zero iff
-- statement:
--   The Local Field construction uses the root Eval eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L61-L66

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

theorem GroundTheory.LocalField.rootEval_eq_zero_iff (F : B⟦X⟧) :
    rootEval hP F = 0 ↔ F ∈ Ideal.span {(P : B⟦X⟧)} := by sorry
