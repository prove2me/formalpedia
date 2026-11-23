-- Prove2me | Theorems.Thm_GroundTheory_LocalField_rootEval_coe
-- name    : GroundTheory.LocalField.rootEval_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:41.650896+00:00
-- url     : https://prove2.me/theorems/c4a28045-4750-49f8-8736-c2c8044eb499
-- title:
--   Local Field: root Eval coe
-- statement:
--   The Local Field construction uses the root Eval coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L46-L50

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

theorem GroundTheory.LocalField.rootEval_coe (p : Polynomial B) : rootEval hP (p : B⟦X⟧) = AdjoinRoot.mk P p := by sorry
