-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_index_lt
-- name    : GroundTheory.Automorphic.MeasurablePartition.index_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:40.791916+00:00
-- url     : https://prove2.me/theorems/aa90537b-e571-44e8-b1ce-b7d98960e539
-- title:
--   Measurable Partition: index lt
-- statement:
--   The Measurable Partition construction uses the index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L50-L51

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
open GroundTheory.Automorphic.MeasurablePartition
variable {X : Type*} [MeasurableSpace X]
variable (p : MeasurablePartition X)

theorem GroundTheory.Automorphic.MeasurablePartition.index_lt (x : X) : p.index x < p.n := by sorry
