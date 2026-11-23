-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_rem
-- name    : GroundTheory.Automorphic.LineKernel.integrable_rem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:17.009538+00:00
-- url     : https://prove2.me/theorems/d20a06df-8d2d-477e-9a10-6b322b03f354
-- title:
--   Line Kernel: integrable rem
-- statement:
--   The Line Kernel construction uses the integrable rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L211-L212

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

theorem GroundTheory.Automorphic.LineKernel.integrable_rem {a r : ℝ} (hr : 0 < r) : Integrable (rem a r) := by sorry
