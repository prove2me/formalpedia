-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_L2Kernel_kernelOp_isHilbertSchmidt
-- name    : GroundTheory.Automorphic.L2Kernel.kernelOp_isHilbertSchmidt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:12.015805+00:00
-- url     : https://prove2.me/theorems/26d0f898-face-49a8-a024-620a079aae98
-- title:
--   L2 Kernel: kernel Op is Hilbert Schmidt
-- statement:
--   The L2 Kernel construction uses the kernel Op is Hilbert Schmidt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtKernel.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtKernel.lean#L192-L193

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.L2Kernel
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]
variable (k : Lp 𝕜 2 (μ.prod ν))

theorem GroundTheory.Automorphic.L2Kernel.kernelOp_isHilbertSchmidt : IsHilbertSchmidt (kernelOp k) := by sorry
