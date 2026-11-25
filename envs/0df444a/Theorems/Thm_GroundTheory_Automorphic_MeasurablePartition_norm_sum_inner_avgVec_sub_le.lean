-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_norm_sum_inner_avgVec_sub_le
-- name    : GroundTheory.Automorphic.MeasurablePartition.norm_sum_inner_avgVec_sub_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:04:44.9045+00:00
-- url     : https://prove2.me/theorems/c4bbe2cc-58ea-4566-a707-5ff3bdfb3170
-- title:
--   Measurable Partition: norm sum inner avg Vec sub le
-- statement:
--   The Measurable Partition construction uses the norm sum inner avg Vec sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L146-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L146-L214

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open GroundTheory.Automorphic.MeasurablePartition
variable (p : MeasurablePartition X)

theorem GroundTheory.Automorphic.MeasurablePartition.norm_sum_inner_avgVec_sub_le (k : C(X × X, ℂ)) {ε : ℝ}
    (hk : ∀ i, ∀ x ∈ p.E i, ∀ y ∈ p.E i, ‖k (x, y) - k (x, x)‖ ≤ ε) :
    ‖∑ i : p.nonnull μ, ⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ -
      ∫ x, k (x, x) ∂μ‖ ≤ ε * μ.real univ := by sorry
