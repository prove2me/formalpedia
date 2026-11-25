-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_of_nonneg
-- name    : GroundTheory.Automorphic.LineKernel.kern_of_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:11.481606+00:00
-- url     : https://prove2.me/theorems/11280c6e-c09a-426a-8edd-661a4cf893e3
-- title:
--   Line Kernel: kern of nonneg
-- statement:
--   The Line Kernel construction uses the kern of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L70-L71

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

theorem GroundTheory.Automorphic.LineKernel.kern_of_nonneg {a r t : ℝ} (ht : 0 ≤ t) : kern a r t = a * exp (-a * t) * cutoff r t := by sorry
