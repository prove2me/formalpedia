-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_le_one
-- name    : GroundTheory.Automorphic.LineKernel.cutoff_le_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:50.942027+00:00
-- url     : https://prove2.me/theorems/7afb7308-3411-4cd0-9174-19c80027d810
-- title:
--   Line Kernel: cutoff le one
-- statement:
--   The Line Kernel construction uses the cutoff le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L32-L33

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

theorem GroundTheory.Automorphic.LineKernel.cutoff_le_one (r t : ℝ) : cutoff r t ≤ 1 := by sorry
