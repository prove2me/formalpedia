-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLeft_eq_of_one_lt
-- name    : GlobalTheory.ZetaLeft.eq_of_one_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:53.735212+00:00
-- url     : https://prove2.me/theorems/8e15c7d1-f368-46c7-a4ba-4bdb5001b790
-- title:
--   Zeta Left: eq of one lt
-- statement:
--   The Zeta Left construction uses the eq of one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L136-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L136-L166

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

theorem GlobalTheory.ZetaLeft.eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by sorry
