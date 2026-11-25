-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_finePart_isFine
-- name    : GroundTheory.Automorphic.finePart_isFine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:19.741236+00:00
-- url     : https://prove2.me/theorems/d9482b3b-ab81-4e71-84ce-4436a5bae63d
-- title:
--   Automorphic: fine Part is Fine
-- statement:
--   The Automorphic construction uses the fine Part is Fine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L146-L149

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology Uniformity UniformSpace Function
open MeasurablePartition
variable (X : Type*) [UniformSpace X]
variable {X}
variable [MeasurableSpace X] [CompactSpace X] [OpensMeasurableSpace X]

theorem GroundTheory.Automorphic.finePart_isFine {V : SetRel X X} (hV : V ∈ 𝓤 X) : (finePart V).IsFine V := by sorry
