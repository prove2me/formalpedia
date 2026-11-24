-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_le
-- name    : GroundTheory.Automorphic.LineKernel.kern_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:22.361775+00:00
-- url     : https://prove2.me/theorems/2c0e4e83-35cf-4cdc-9c2b-5482eb4abdd2
-- title:
--   Line Kernel: kern le
-- statement:
--   The Line Kernel construction uses the kern le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L80-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L80-L89

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

theorem GroundTheory.Automorphic.LineKernel.kern_le {a : ℝ} (ha : 0 ≤ a) (r t : ℝ) : kern a r t ≤ a := by sorry
