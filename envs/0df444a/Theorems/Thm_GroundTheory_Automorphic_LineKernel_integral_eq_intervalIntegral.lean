-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_eq_intervalIntegral
-- name    : GroundTheory.Automorphic.LineKernel.integral_eq_intervalIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:04.515592+00:00
-- url     : https://prove2.me/theorems/9edabdd6-4d08-42bc-bb68-8f3cd84ee964
-- title:
--   Line Kernel: integral eq interval Integral
-- statement:
--   The Line Kernel construction uses the integral eq interval Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L123-L127

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.integral_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {b : ℝ} (hb : 0 ≤ b) (hg : ∀ t ∉ Icc 0 b, g t = 0) :
    ∫ t, g t = ∫ t in (0 : ℝ)..b, g t := by sorry
