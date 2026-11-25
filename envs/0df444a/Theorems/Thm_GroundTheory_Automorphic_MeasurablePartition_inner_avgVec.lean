-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_inner_avgVec
-- name    : GroundTheory.Automorphic.MeasurablePartition.inner_avgVec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:36.270678+00:00
-- url     : https://prove2.me/theorems/47bef989-fadc-47de-a8ce-a80538cac010
-- title:
--   Measurable Partition: inner avg Vec
-- statement:
--   The Measurable Partition construction uses the inner avg Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L75-L77

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
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open GroundTheory.Automorphic.MeasurablePartition
variable (p : MeasurablePartition X)

theorem GroundTheory.Automorphic.MeasurablePartition.inner_avgVec (i : p.nonnull μ) (f : Lp ℂ 2 μ) :
    ⟪p.avgVec μ i, f⟫_ℂ = (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) * ∫ x in p.E i, f x ∂μ := by sorry
