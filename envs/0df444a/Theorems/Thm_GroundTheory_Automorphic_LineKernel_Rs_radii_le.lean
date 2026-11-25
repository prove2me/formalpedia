-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_Rs_radii_le
-- name    : GroundTheory.Automorphic.LineKernel.Rs_radii_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:27.130029+00:00
-- url     : https://prove2.me/theorems/93e54b48-6cbc-404f-bef5-25f9dd78eefb
-- title:
--   Line Kernel: Rs radii le
-- statement:
--   The Line Kernel construction uses the Rs radii le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L20-L26

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.Rs_radii_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) : Rs (radii ε) n ≤ ε / 2 := by sorry
