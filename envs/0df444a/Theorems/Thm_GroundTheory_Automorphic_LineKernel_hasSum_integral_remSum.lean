-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasSum_integral_remSum
-- name    : GroundTheory.Automorphic.LineKernel.hasSum_integral_remSum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:04:38.524793+00:00
-- url     : https://prove2.me/theorems/8ce5c130-3cd1-4294-91a7-967a9bffca93
-- title:
--   Line Kernel: has Sum integral rem Sum
-- statement:
--   The Line Kernel construction uses the has Sum integral rem Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L192-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L192-L220

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

theorem GroundTheory.Automorphic.LineKernel.hasSum_integral_remSum {F : ℝ → ℂ} (hF : Continuous F) {B : ℝ}
    (hB : ∀ t ∈ Icc (-ε) ε, ‖F t‖ ≤ B) :
    HasSum (fun j => ∫ t, F t * ρ a (radii ε) j t) (∫ t, F t * remSum (ε := ε) (a := a) t) := by sorry
