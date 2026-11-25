-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_LineKernel_sum_sc_succ
-- name    : GroundTheory.Automorphic.LineKernel.sum_sc_succ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:19.256682+00:00
-- url     : https://prove2.me/theorems/b9fb50d5-25d7-4da1-87fb-8102e93011f4
-- title:
--   Line Kernel: sum sc succ
-- statement:
--   The Line Kernel construction uses the sum sc succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L141-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean#L141-L155

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

theorem GroundTheory.Automorphic.LineKernel.sum_sc_succ (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℂ) :
    ∑ p ∈ Finset.range (n + 2), sc a (n + 1) p * d p =
      ∑ p ∈ Finset.range (n + 1), sc a n p * d p -
        (a n : ℂ)⁻¹ * ∑ p ∈ Finset.range (n + 1), sc a n p * d (p + 1) := by sorry
