-- Prove2me | Theorems.Thm_GroundTheory_LocalField_root_pow_mem_map
-- name    : GroundTheory.LocalField.root_pow_mem_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:50.87273+00:00
-- url     : https://prove2.me/theorems/09a10db1-1fbd-4fe7-906c-cbf1ec673fb6
-- title:
--   Local Field: root pow mem map
-- statement:
--   The Local Field construction uses the root pow mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L95-L107

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

theorem GroundTheory.LocalField.root_pow_mem_map (hP : P.IsDistinguishedAt I) :
    AdjoinRoot.root P ^ P.natDegree ∈ I.map (AdjoinRoot.of P) := by sorry
