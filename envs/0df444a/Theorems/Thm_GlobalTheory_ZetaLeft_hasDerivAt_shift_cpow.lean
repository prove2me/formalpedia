-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLeft_hasDerivAt_shift_cpow
-- name    : GlobalTheory.ZetaLeft.hasDerivAt_shift_cpow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:40.849355+00:00
-- url     : https://prove2.me/theorems/c5616acf-3762-4c5d-9ac7-9948f62e8ad5
-- title:
--   Zeta Left: has Deriv At shift cpow
-- statement:
--   The Zeta Left construction uses the has Deriv At shift cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L14-L19

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

theorem GlobalTheory.ZetaLeft.hasDerivAt_shift_cpow {a t : ℝ} (h : 0 < a + t) (c : ℂ) :
    HasDerivAt (fun z : ℂ => ((a : ℂ) + z) ^ c) (c * ((a : ℂ) + t) ^ (c - 1)) (t : ℂ) := by sorry
