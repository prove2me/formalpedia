-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_integrable_of_continuous_compact
-- name    : GroundTheory.Automorphic.integrable_of_continuous_compact
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:09.484701+00:00
-- url     : https://prove2.me/theorems/00178dca-d4b7-4d4b-a267-c1bb71f69fa3
-- title:
--   Automorphic: integrable of continuous compact
-- statement:
--   The Automorphic construction uses the integrable of continuous compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L109-L112

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
omit [T2Space X]

theorem GroundTheory.Automorphic.integrable_of_continuous_compact {f : X → ℂ} (hf : Continuous f) (ν : Measure X)
    [IsFiniteMeasure ν] : Integrable f ν := by sorry
