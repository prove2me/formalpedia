-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contKernelOp_apply_ae
-- name    : GroundTheory.Automorphic.contKernelOp_apply_ae
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:00:28.02068+00:00
-- url     : https://prove2.me/theorems/1d2af521-dd2d-4a31-877e-bbc639a97d7d
-- title:
--   Automorphic: cont Kernel Op apply ae
-- statement:
--   The Automorphic construction uses the cont Kernel Op apply ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/KernelTrace.lean#L34-L36

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
  [BorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

theorem GroundTheory.Automorphic.contKernelOp_apply_ae (k : C(X × X, ℂ)) (f : Lp ℂ 2 μ) :
    contKernelOp μ k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂μ := by sorry
