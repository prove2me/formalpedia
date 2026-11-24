-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLeft_differentiable_emE
-- name    : GlobalTheory.ZetaLeft.differentiable_emE
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:59.179795+00:00
-- url     : https://prove2.me/theorems/6e54d201-5caa-48d5-9b3a-16088dbf4013
-- title:
--   Zeta Left: differentiable em E
-- statement:
--   The Zeta Left construction uses the differentiable em E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L102-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L102-L108

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

theorem GlobalTheory.ZetaLeft.differentiable_emE {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emE x) := by sorry
