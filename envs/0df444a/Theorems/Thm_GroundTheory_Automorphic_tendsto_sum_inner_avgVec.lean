-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_tendsto_sum_inner_avgVec
-- name    : GroundTheory.Automorphic.tendsto_sum_inner_avgVec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:23.610963+00:00
-- url     : https://prove2.me/theorems/9cfaa87c-c436-4b96-90be-086d48144276
-- title:
--   Automorphic: tendsto sum inner avg Vec
-- statement:
--   The Automorphic construction uses the tendsto sum inner avg Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L335-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L335-L359

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

theorem GroundTheory.Automorphic.tendsto_sum_inner_avgVec (k : C(X × X, ℂ)) :
    Tendsto (fun V => ∑ i : (finePart V).nonnull μ,
      ⟪(finePart V).avgVec μ i, contKernelOp μ k ((finePart V).avgVec μ i)⟫_ℂ) (fineFilter X)
      (𝓝 (∫ x, k (x, x) ∂μ)) := by sorry
