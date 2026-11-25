-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_antitone_cutoff
-- name    : GroundTheory.Automorphic.LineKernel.antitone_cutoff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:12.761318+00:00
-- url     : https://prove2.me/theorems/5b12fbee-24a6-4d60-8c1f-d27aaabd426d
-- title:
--   Line Kernel: antitone cutoff
-- statement:
--   The Line Kernel construction uses the antitone cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L196-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineKernel.lean#L196-L201

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

theorem GroundTheory.Automorphic.LineKernel.antitone_cutoff {r : ℝ} (hr : 0 < r) : Antitone (cutoff r) := by sorry
