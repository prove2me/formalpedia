-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_L2Kernel_exists_row
-- name    : GroundTheory.Automorphic.L2Kernel.exists_row
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:30.477342+00:00
-- url     : https://prove2.me/theorems/be6c6e1e-eab1-4cae-8486-001927109795
-- title:
--   L2 Kernel: exists row
-- statement:
--   The L2 Kernel construction uses the exists row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtKernel.lean#L153-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtKernel.lean#L153-L169

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

theorem GroundTheory.Automorphic.L2Kernel.exists_row {x : X} (hx : ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν < ∞) :
    ∃ h : Lp 𝕜 2 ν, ‖h‖ₑ ^ 2 = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∧
      ∀ f : Lp 𝕜 2 ν, kernelFun (ν := ν) k f x = ⟪h, f⟫_𝕜 := by sorry
