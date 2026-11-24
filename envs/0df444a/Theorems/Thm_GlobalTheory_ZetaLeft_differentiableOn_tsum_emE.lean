-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLeft_differentiableOn_tsum_emE
-- name    : GlobalTheory.ZetaLeft.differentiableOn_tsum_emE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:47.640256+00:00
-- url     : https://prove2.me/theorems/c2c96d54-0db8-48bc-967b-f65d066f4228
-- title:
--   Zeta Left: differentiable On tsum em E
-- statement:
--   The Zeta Left construction uses the differentiable On tsum em E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L110-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L110-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft

theorem GlobalTheory.ZetaLeft.differentiableOn_tsum_emE :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, emE ((n : ℝ) + 1) s) {s : ℂ | -(15/8 : ℝ) < s.re} := by sorry
