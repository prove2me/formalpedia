-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_measurable_kern
-- name    : GroundTheory.Automorphic.LineKernel.measurable_kern
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:08.068182+00:00
-- url     : https://prove2.me/theorems/88c3fdbe-14d3-4397-9cf3-0600591b743f
-- title:
--   Line Kernel: measurable kern
-- statement:
--   The Line Kernel construction uses the measurable kern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L91-L94

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

theorem GroundTheory.Automorphic.LineKernel.measurable_kern (a r : ℝ) : Measurable (kern a r) := by sorry
