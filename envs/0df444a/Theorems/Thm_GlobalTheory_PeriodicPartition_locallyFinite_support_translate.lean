-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicPartition_locallyFinite_support_translate
-- name    : GlobalTheory.PeriodicPartition.locallyFinite_support_translate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:11.943121+00:00
-- url     : https://prove2.me/theorems/0de884e5-9409-4c73-87ad-0d3eba171d76
-- title:
--   Periodic Partition: locally Finite support translate
-- statement:
--   The Periodic Partition construction uses the locally Finite support translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothPeriodicPartitionOfUnity.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothPeriodicPartitionOfUnity.lean#L14-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicPartition
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
open Complex Matrix
open scoped ContDiff BigOperators Real Topology Manifold
open scoped Pointwise
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.PeriodicPartition.locallyFinite_support_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) :
    LocallyFinite fun l : Λ => Function.support fun z : E => φ (z + l) := by sorry
