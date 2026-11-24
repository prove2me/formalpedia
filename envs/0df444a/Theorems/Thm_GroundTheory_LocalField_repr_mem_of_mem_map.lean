-- Prove2me | Theorems.Thm_GroundTheory_LocalField_repr_mem_of_mem_map
-- name    : GroundTheory.LocalField.repr_mem_of_mem_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:06.060201+00:00
-- url     : https://prove2.me/theorems/207133fe-da63-4736-9d32-f2e4c81ecd28
-- title:
--   Local Field: repr mem of mem map
-- statement:
--   The Local Field construction uses the repr mem of mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LubinTateReciprocity/RootEval.lean#L109-L119

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

theorem GroundTheory.LocalField.repr_mem_of_mem_map (hP : P.Monic) (J : Ideal B) {z : AdjoinRoot P}
    (hz : z ∈ J.map (AdjoinRoot.of P)) (i : Fin (AdjoinRoot.powerBasis' hP).dim) :
    (AdjoinRoot.powerBasis' hP).basis.repr z i ∈ J := by sorry
