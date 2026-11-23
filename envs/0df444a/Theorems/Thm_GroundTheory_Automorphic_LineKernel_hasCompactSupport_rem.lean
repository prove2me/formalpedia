-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_rem
-- name    : GroundTheory.Automorphic.LineKernel.hasCompactSupport_rem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:00.054661+00:00
-- url     : https://prove2.me/theorems/5a453de9-9b1a-42fb-96b4-c972f2cb1a36
-- title:
--   Line Kernel: has Compact Support rem
-- statement:
--   The Line Kernel construction uses the has Compact Support rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L120-L121

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

theorem GroundTheory.Automorphic.LineKernel.hasCompactSupport_rem {a r : ℝ} (hr : 0 < r) : HasCompactSupport (rem a r) := by sorry
