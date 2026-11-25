-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_KC_succ
-- name    : GroundTheory.Automorphic.LineKernel.KC_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:17.26116+00:00
-- url     : https://prove2.me/theorems/0de0c629-589e-4ccd-934f-6e7c9147267f
-- title:
--   Line Kernel: KC succ
-- statement:
--   The Line Kernel construction uses the KC succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L264-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L264-L265

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

theorem GroundTheory.Automorphic.LineKernel.KC_succ (n : ℕ) : KC a r (n + 1) = KC a r n ⋆[mul ℂ ℂ] kC a r (n + 1) := by sorry
