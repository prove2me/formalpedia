-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contKernelOp_comp
-- name    : GroundTheory.Automorphic.contKernelOp_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:55:08.224177+00:00
-- url     : https://prove2.me/theorems/1090c008-a486-49a5-95d0-9cbc81635211
-- title:
--   Automorphic: cont Kernel Op comp
-- statement:
--   The Automorphic construction uses the cont Kernel Op comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTraceComp.lean#L81-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTraceComp.lean#L81-L115

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTraceComp
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
open scoped InnerProductSpace ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem GroundTheory.Automorphic.contKernelOp_comp (a b : C(X × X, ℂ)) :
    (contKernelOp μ a).comp (contKernelOp μ b) = contKernelOp μ (compKernel μ a b) := by sorry
