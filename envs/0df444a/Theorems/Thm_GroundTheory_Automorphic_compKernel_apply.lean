-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_compKernel_apply
-- name    : GroundTheory.Automorphic.compKernel_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:17.364125+00:00
-- url     : https://prove2.me/theorems/7e6f9d8b-83d4-45c5-9ab5-156e15a205bd
-- title:
--   Automorphic: comp Kernel apply
-- statement:
--   The Automorphic construction uses the comp Kernel apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTraceComp.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTraceComp.lean#L78-L79

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

theorem GroundTheory.Automorphic.compKernel_apply (a b : C(X × X, ℂ)) (z : X × X) :
    compKernel μ a b z = ∫ y, a (z.1, y) * b (y, z.2) ∂μ := by sorry
