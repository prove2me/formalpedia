-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_L2Kernel_kernelOp_apply_ae
-- name    : GroundTheory.Automorphic.L2Kernel.kernelOp_apply_ae
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:05.256646+00:00
-- url     : https://prove2.me/theorems/62c52051-7e1c-4465-a229-734259dbc44f
-- title:
--   L2 Kernel: kernel Op apply ae
-- statement:
--   The L2 Kernel construction uses the kernel Op apply ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtKernel.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtKernel.lean#L149-L151

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

theorem GroundTheory.Automorphic.L2Kernel.kernelOp_apply_ae (f : Lp 𝕜 2 ν) :
    kernelOp k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν := by sorry
