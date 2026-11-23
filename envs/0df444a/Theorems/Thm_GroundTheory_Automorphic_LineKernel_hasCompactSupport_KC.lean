-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_KC
-- name    : GroundTheory.Automorphic.LineKernel.hasCompactSupport_KC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:26.137691+00:00
-- url     : https://prove2.me/theorems/7d0b9552-a659-4221-9531-258d5458ec5a
-- title:
--   Line Kernel: has Compact Support KC
-- statement:
--   The Line Kernel construction uses the has Compact Support KC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L269-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L269-L270

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
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem GroundTheory.Automorphic.LineKernel.hasCompactSupport_KC (n : ℕ) : HasCompactSupport (KC a r n) := by sorry
