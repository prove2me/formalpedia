-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_tendsto_coef
-- name    : GroundTheory.Automorphic.LineKernel.tendsto_coef
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:04:12.008026+00:00
-- url     : https://prove2.me/theorems/e01d2152-17e5-4f7e-8035-e846aa069a24
-- title:
--   Line Kernel: tendsto coef
-- statement:
--   The Line Kernel construction uses the tendsto coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L281-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L281-L283

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
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg

theorem GroundTheory.Automorphic.LineKernel.tendsto_coef (p : ℕ) : Tendsto (fun n => coef a n p) atTop (𝓝 (climit (a := a) p)) := by sorry
