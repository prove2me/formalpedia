-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_trace_contKernelOp_of_uniformSpace
-- name    : GroundTheory.Automorphic.trace_contKernelOp_of_uniformSpace
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:04.105691+00:00
-- url     : https://prove2.me/theorems/2b2e4e7f-3953-44da-96ea-2d4c955c0ac5
-- title:
--   Automorphic: trace cont Kernel Op of uniform Space
-- statement:
--   The Automorphic construction uses the trace cont Kernel Op of uniform Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L361-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L361-L368

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
variable {X : Type*} [UniformSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open MeasurablePartition

theorem GroundTheory.Automorphic.trace_contKernelOp_of_uniformSpace [μ.WeaklyRegular] (k : C(X × X, ℂ))
    (hT : IsTraceClass (contKernelOp μ k)) : trace (contKernelOp μ k) = ∫ x, k (x, x) ∂μ := by sorry
