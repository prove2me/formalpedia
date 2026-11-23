-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_index_eq_iff
-- name    : GroundTheory.Automorphic.MeasurablePartition.index_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:19.300884+00:00
-- url     : https://prove2.me/theorems/4fba6825-4f93-4d33-af66-3c2b0716eb45
-- title:
--   Measurable Partition: index eq iff
-- statement:
--   The Measurable Partition construction uses the index eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L56-L59

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

theorem GroundTheory.Automorphic.MeasurablePartition.index_eq_iff {x : X} {i : ℕ} : p.index x = i ↔ x ∈ p.E i := by sorry
