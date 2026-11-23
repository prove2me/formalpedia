-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_convolution_mul_eq_real
-- name    : GroundTheory.Automorphic.LineKernel.convolution_mul_eq_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:01.18629+00:00
-- url     : https://prove2.me/theorems/39576b20-3a83-42a5-acdf-65b848b37a4a
-- title:
--   Line Kernel: convolution mul eq real
-- statement:
--   The Line Kernel construction uses the convolution mul eq real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineBounds.lean#L27-L28

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
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

theorem GroundTheory.Automorphic.LineKernel.convolution_mul_eq_real (f g : ℝ → ℂ) : (f ⋆[mul ℂ ℂ] g) = (f ⋆[mul ℝ ℂ] g) := by sorry
