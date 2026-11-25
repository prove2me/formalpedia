-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_inner_avgVec_contKernelOp
-- name    : GroundTheory.Automorphic.MeasurablePartition.inner_avgVec_contKernelOp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:04:31.973018+00:00
-- url     : https://prove2.me/theorems/9a00f4c7-0885-4f9a-89ce-d05839337806
-- title:
--   Measurable Partition: inner avg Vec cont Kernel Op
-- statement:
--   The Measurable Partition construction uses the inner avg Vec cont Kernel Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L128-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L128-L144

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

theorem GroundTheory.Automorphic.MeasurablePartition.inner_avgVec_contKernelOp (k : C(X × X, ℂ)) (i : p.nonnull μ) :
    ⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ =
      (((μ.real (p.E i))⁻¹ : ℝ) : ℂ) * ∫ x in p.E i, ∫ y in p.E i, k (x, y) ∂μ ∂μ := by sorry
