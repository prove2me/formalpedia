-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_iteratedDeriv_deriv_cutoff
-- name    : GroundTheory.Automorphic.LineKernel.hasCompactSupport_iteratedDeriv_deriv_cutoff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:51.138925+00:00
-- url     : https://prove2.me/theorems/4171ca11-4ba5-4966-beec-a4dafc74486b
-- title:
--   Line Kernel: has Compact Support iterated Deriv deriv cutoff
-- statement:
--   The Line Kernel construction uses the has Compact Support iterated Deriv deriv cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L384-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L384-L387

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

theorem GroundTheory.Automorphic.LineKernel.hasCompactSupport_iteratedDeriv_deriv_cutoff {r : ℝ} (hr : 0 < r) (i : ℕ) :
    HasCompactSupport (iteratedDeriv i (deriv (cutoff r))) := by sorry
