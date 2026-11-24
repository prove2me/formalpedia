-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_ofReal_convolution
-- name    : GroundTheory.Automorphic.LineKernel.ofReal_convolution
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:59.128914+00:00
-- url     : https://prove2.me/theorems/503a03f3-f4cd-475d-a331-e81f632a0dfc
-- title:
--   Line Kernel: of Real convolution
-- statement:
--   The Line Kernel construction uses the of Real convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L40-L44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
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
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel

theorem GroundTheory.Automorphic.LineKernel.ofReal_convolution (f g : ℝ → ℝ) (x : ℝ) :
    (((f ⋆[mul ℝ ℝ] g) x : ℝ) : ℂ) =
      ((fun t => (f t : ℂ)) ⋆[mul ℂ ℂ] (fun t => (g t : ℂ))) x := by sorry
