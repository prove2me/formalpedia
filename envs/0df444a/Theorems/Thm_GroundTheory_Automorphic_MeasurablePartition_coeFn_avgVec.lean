-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_coeFn_avgVec
-- name    : GroundTheory.Automorphic.MeasurablePartition.coeFn_avgVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:30.80788+00:00
-- url     : https://prove2.me/theorems/4db7e2df-ac24-4bb6-9148-77398a70a4d2
-- title:
--   Measurable Partition: coe Fn avg Vec
-- statement:
--   The Measurable Partition construction uses the coe Fn avg Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L119-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L119-L126

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
omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [BorelSpace X]

theorem GroundTheory.Automorphic.MeasurablePartition.coeFn_avgVec (i : p.nonnull μ) :
    p.avgVec μ i =ᵐ[μ] fun y => (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) *
      (p.E i).indicator (fun _ => (1 : ℂ)) y := by sorry
