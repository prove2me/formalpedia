-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_eq_zero_of_neg
-- name    : GroundTheory.Automorphic.LineKernel.kern_eq_zero_of_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:09.967666+00:00
-- url     : https://prove2.me/theorems/cd554528-c056-4d13-92d4-63942a21a8c9
-- title:
--   Line Kernel: kern eq zero of neg
-- statement:
--   The Line Kernel construction uses the kern eq zero of neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L64-L65

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

theorem GroundTheory.Automorphic.LineKernel.kern_eq_zero_of_neg {a r t : ℝ} (ht : t < 0) : kern a r t = 0 := by sorry
