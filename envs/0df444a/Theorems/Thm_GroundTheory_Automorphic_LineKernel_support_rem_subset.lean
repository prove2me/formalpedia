-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_rem_subset
-- name    : GroundTheory.Automorphic.LineKernel.support_rem_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:18.06248+00:00
-- url     : https://prove2.me/theorems/3809f501-6ab1-477c-9ce1-c743324ee9c6
-- title:
--   Line Kernel: support rem subset
-- statement:
--   The Line Kernel construction uses the support rem subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L117-L118

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

theorem GroundTheory.Automorphic.LineKernel.support_rem_subset {a r : ℝ} (hr : 0 < r) : support (rem a r) ⊆ Icc r (2 * r) := by sorry
