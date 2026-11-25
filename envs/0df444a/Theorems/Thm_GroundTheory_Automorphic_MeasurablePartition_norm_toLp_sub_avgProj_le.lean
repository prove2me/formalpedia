-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_norm_toLp_sub_avgProj_le
-- name    : GroundTheory.Automorphic.MeasurablePartition.norm_toLp_sub_avgProj_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:44.810035+00:00
-- url     : https://prove2.me/theorems/56c5bd4d-e94c-48a2-8efd-35ecff515a15
-- title:
--   Measurable Partition: norm to Lp sub avg Proj le
-- statement:
--   The Measurable Partition construction uses the norm to Lp sub avg Proj le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L238-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L238-L288

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
omit [T2Space X]

theorem GroundTheory.Automorphic.MeasurablePartition.norm_toLp_sub_avgProj_le {V : SetRel X X} (hp : p.IsFine V) (f : C(X, ℂ)) {ε : ℝ}
    (hε : 0 ≤ ε) (hf : ∀ x y, (x, y) ∈ V → ‖f x - f y‖ ≤ ε) :
    ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ f - p.avgProj μ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f)‖ ≤
      (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * ε := by sorry
