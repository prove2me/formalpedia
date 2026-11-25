-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_tendsto_finePart_avgProj
-- name    : GroundTheory.Automorphic.tendsto_finePart_avgProj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:39.425733+00:00
-- url     : https://prove2.me/theorems/695869a6-6b10-4841-b48c-5a35a1441c32
-- title:
--   Automorphic: tendsto fine Part avg Proj
-- statement:
--   The Automorphic construction uses the tendsto fine Part avg Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L301-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L301-L333

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

theorem GroundTheory.Automorphic.tendsto_finePart_avgProj [μ.WeaklyRegular] (y : Lp ℂ 2 μ) :
    Tendsto (fun V => (finePart V).avgProj μ y) (fineFilter X) (𝓝 y) := by sorry
