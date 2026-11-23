-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLeft_norm_sub_one_mul_riemannZeta_le
-- name    : GlobalTheory.ZetaLeft.norm_sub_one_mul_riemannZeta_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:19.685069+00:00
-- url     : https://prove2.me/theorems/cd434fb7-3169-4138-a0da-bcaf0b3e08b2
-- title:
--   Zeta Left: norm sub one mul riemann Zeta le
-- statement:
--   The Zeta Left construction uses the norm sub one mul riemann Zeta le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L188-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L188-L215

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

theorem GlobalTheory.ZetaLeft.norm_sub_one_mul_riemannZeta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(7/4 : ℝ) ≤ s.re → s ≠ 1 →
      ‖(s - 1) * riemannZeta s‖ ≤ C * (‖s‖ + 2) ^ 5 := by sorry
