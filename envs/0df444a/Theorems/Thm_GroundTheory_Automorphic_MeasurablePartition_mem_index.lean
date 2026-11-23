-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_mem_index
-- name    : GroundTheory.Automorphic.MeasurablePartition.mem_index
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:26.882854+00:00
-- url     : https://prove2.me/theorems/ecc14805-ad2b-4a55-b8bf-4a0f5f57992e
-- title:
--   Measurable Partition: mem index
-- statement:
--   The Measurable Partition construction uses the mem index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L53-L54

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

theorem GroundTheory.Automorphic.MeasurablePartition.mem_index (x : X) : x ∈ p.E (p.index x) := by sorry
