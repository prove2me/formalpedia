-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_kern
-- name    : GroundTheory.Automorphic.LineKernel.integrable_kern
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:05.916057+00:00
-- url     : https://prove2.me/theorems/78c0488b-32fd-4379-8f30-bf51010d03e3
-- title:
--   Line Kernel: integrable kern
-- statement:
--   The Line Kernel construction uses the integrable kern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L96-L103

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

theorem GroundTheory.Automorphic.LineKernel.integrable_kern {a : ℝ} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) : Integrable (kern a r) := by sorry
